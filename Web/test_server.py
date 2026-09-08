"""Integration checks against the actual native Lean executable."""
import http.client
import json
import threading
import unittest
from unittest.mock import patch

from server import BINARY, Handler, MAX_MESSAGE, ThreadingHTTPServer, transform


KEY = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
NONCE = "000000000000004a00000000"


def request(message="Hello", **overrides):
    return {"cipher": "chacha20", "operation": "encrypt", "key": KEY,
            "nonce": NONCE, "message": message, **overrides}


class CipherTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file():
            raise RuntimeError("Run lake build crypto_web before the tests.")

    def test_rfc8439_encryption_vector(self):
        plaintext = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
        expected = "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"
        self.assertEqual(transform(request(plaintext))["result"], expected)
        self.assertEqual(transform(request(expected, operation="decrypt"))["result"], plaintext)

    def test_vigenere_vector_and_normalization(self):
        result = transform(request("Attack at dawn! 123", cipher="vigenere", key="lemon"))
        self.assertEqual(result["result"], "LXFOPVEFRNHR")
        self.assertEqual(transform(request(result["result"], cipher="vigenere", key="LEMON", operation="decrypt"))["result"], "ATTACKATDAWN")

    def test_unicode_multiblock_and_empty_roundtrips(self):
        for message in ("", "Hello 🌍 — café\n你好\x00" * 40, "x" * 63, "x" * 64, "x" * 65):
            with self.subTest(length=len(message)):
                encrypted = transform(request(message))["result"]
                self.assertEqual(len(encrypted), 2 * len(message.encode("utf-8")))
                self.assertEqual(transform(request(encrypted, operation="decrypt"))["result"], message)
        self.assertEqual(transform(request("", cipher="vigenere", key="A"))["result"], "")

    def test_maximum_size(self):
        encrypted = transform(request("a" * MAX_MESSAGE))["result"]
        self.assertEqual(len(encrypted), MAX_MESSAGE * 2)
        self.assertEqual(transform(request(encrypted, operation="decrypt"))["result"], "a" * MAX_MESSAGE)

    def test_invalid_inputs(self):
        invalid = [None, [], {}, request(key="00"), request(key="g" * 64),
                   request(nonce=""), request(nonce="z" * 24), request(nonce=None),
                   request("a", operation="decrypt"), request("xx", operation="decrypt"),
                   request(cipher="unknown"), request(operation="bad"), request(message=42),
                   request("x" * (MAX_MESSAGE + 1)), request("é" * MAX_MESSAGE),
                   request(cipher="vigenere", key=""), request(cipher="vigenere", key="A B"),
                   request(cipher="vigenere", key="é"), request(cipher="vigenere", key="A" * 4097)]
        for data in invalid:
            with self.subTest(data=str(data)[:100]):
                with self.assertRaises(ValueError):
                    transform(data)

    def test_nonce_changes_ciphertext(self):
        self.assertNotEqual(transform(request())["result"], transform(request(nonce="00" * 12))["result"])

    def test_binary_decryption_is_lossless(self):
        # XOR the keystream for an encrypted NUL to construct ciphertext for 0xff.
        keystream = int(transform(request("\x00"))["result"], 16)
        result = transform(request(f"{keystream ^ 255:02x}", operation="decrypt"))
        self.assertEqual(result["encoding"], "hex")
        self.assertEqual(result["result"], "ff")


class HTTPTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        cls.port = cls.server.server_address[1]
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        cls.thread.join()

    def http(self, method="GET", path="/", body=None, headers=None):
        conn = http.client.HTTPConnection("127.0.0.1", self.port, timeout=20)
        try:
            conn.request(method, path, body, headers or {})
            response = conn.getresponse()
            return response.status, dict(response.getheaders()), response.read()
        finally:
            conn.close()

    def test_static_assets_and_repository_isolation(self):
        for path in ("/", "/app.js", "/style.css"):
            status, headers, body = self.http(path=path)
            self.assertEqual(status, 200)
            self.assertTrue(body)
            self.assertEqual(headers["Cache-Control"], "no-store")
            self.assertIn("frame-ancestors 'none'", headers["Content-Security-Policy"])
        for path in ("/../lakefile.toml", "/.git/config", "/Web/Main.lean"):
            self.assertEqual(self.http(path=path)[0], 404)

    def test_encryption_over_http(self):
        status, _, body = self.http("POST", "/api/transform",
                                    json.dumps(request("ATTACKATDAWN", cipher="vigenere", key="LEMON")),
                                    {"Content-Type": "application/json", "Origin": f"http://127.0.0.1:{self.port}"})
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body)["result"], "LXFOPVEFRNHR")

    def test_host_origin_and_content_type_restrictions(self):
        self.assertEqual(self.http(headers={"Host": "attacker.example"})[0], 403)
        self.assertEqual(self.http(headers={"Origin": "https://attacker.example"})[0], 403)
        self.assertEqual(self.http(headers={"Sec-Fetch-Site": "cross-site"})[0], 403)
        self.assertEqual(self.http("POST", "/api/transform", "{}", {"Content-Type": "text/plain"})[0], 415)
        self.assertEqual(self.http("POST", "/api/transform", "{", {"Content-Type": "application/json"})[0], 400)
        self.assertEqual(self.http("POST", "/api/transform", "{}", {"Content-Type": "application/json", "Content-Length": "2000000"})[0], 413)

    def test_aead_authentication_failure_releases_no_plaintext(self):
        original = request("private plaintext", cipher="chacha20-poly1305", aad="header")
        headers = {"Content-Type": "application/json"}
        status, _, body = self.http("POST", "/api/transform", json.dumps(original), headers)
        self.assertEqual(status, 200)
        encrypted = json.loads(body)
        opening = {**original, "operation": "decrypt", "message": encrypted["result"], "tag": encrypted["tag"]}
        status, _, body = self.http("POST", "/api/transform", json.dumps(opening), headers)
        self.assertEqual(status, 200)
        self.assertTrue(json.loads(body)["authenticated"])
        opening["aad"] = "tampered header"
        status, _, body = self.http("POST", "/api/transform", json.dumps(opening), headers)
        self.assertEqual(status, 400)
        self.assertEqual(set(json.loads(body)), {"error"})
        self.assertIn(b"Authentication failed", body)
        self.assertNotIn(b"private plaintext", body)

    def test_errors_do_not_expose_process_details(self):
        with patch("server.transform", side_effect=RuntimeError("secret details")):
            status, _, body = self.http("POST", "/api/transform", "{}", {"Content-Type": "application/json"})
        self.assertEqual(status, 500)
        self.assertNotIn(b"secret details", body)


class AEADTests(unittest.TestCase):
    def test_rfc8439_aead_vector(self):
        original = request(
            "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.",
            cipher="chacha20-poly1305",
            key="808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f",
            nonce="070000004041424344454647", aad="50515253c0c1c2c3c4c5c6c7", aad_encoding="hex")
        encrypted = transform(original)
        expected = ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6"
                    "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36"
                    "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc"
                    "3ff4def08e4b7a9de576d26586cec64b6116")
        self.assertEqual(encrypted["result"], expected)
        self.assertEqual(encrypted["tag"], "1ae10b594f09e26a7e902ecbd0600691")
        decrypted = transform({**original, "operation": "decrypt", "message": expected, "tag": encrypted["tag"]})
        self.assertEqual(decrypted["result"], original["message"])
        self.assertTrue(decrypted["authenticated"])

    def test_tampering_each_input_is_rejected(self):
        original = request("Never release this plaintext", cipher="chacha20-poly1305", aad="context")
        encrypted = transform(original)
        opening = {**original, "operation": "decrypt", "message": encrypted["result"], "tag": encrypted["tag"]}
        for name in ("key", "nonce", "aad", "message", "tag"):
            modified = dict(opening)
            value = modified[name]
            modified[name] = ("1" if value[0] == "0" else "0") + value[1:]
            with self.subTest(field=name), self.assertRaisesRegex(ValueError, "Authentication failed"):
                transform(modified)

    def test_aead_empty_unicode_and_boundary_roundtrips(self):
        for size in (0, 1, 15, 16, 17, 63, 64, 65, MAX_MESSAGE):
            original = request("x" * size, cipher="chacha20-poly1305", aad="文件 🌍" if size else "")
            encrypted = transform(original)
            decrypted = transform({**original, "operation": "decrypt", "message": encrypted["result"], "tag": encrypted["tag"]})
            self.assertEqual(decrypted["result"], original["message"])
            self.assertTrue(decrypted["authenticated"])
        original = request("Bonjour 🌍\n你好\x00" * 20, cipher="chacha20-poly1305")
        encrypted = transform(original)
        self.assertEqual(transform({**original, "operation": "decrypt", "message": encrypted["result"], "tag": encrypted["tag"]})["result"], original["message"])

    def test_aad_encodings_agree_and_limits(self):
        base = request(cipher="chacha20-poly1305", aad="café")
        self.assertEqual(transform(base), transform({**base, "aad": "café".encode().hex(), "aad_encoding": "hex"}))
        self.assertEqual(len(transform({**base, "aad": "x" * MAX_MESSAGE})["tag"]), 32)
        invalid = [{"aad": None}, {"aad_encoding": "unknown"}, {"aad": "f", "aad_encoding": "hex"},
                   {"aad": "zz", "aad_encoding": "hex"}, {"aad": "x" * (MAX_MESSAGE + 1)},
                   {"aad": "00" * (MAX_MESSAGE + 1), "aad_encoding": "hex"},
                   {"operation": "decrypt"}, {"operation": "decrypt", "tag": "00"},
                   {"operation": "decrypt", "tag": "g" * 32}]
        for overrides in invalid:
            with self.subTest(fields=list(overrides)), self.assertRaises(ValueError):
                transform({**base, "message": "", **overrides})


if __name__ == "__main__":
    unittest.main()
