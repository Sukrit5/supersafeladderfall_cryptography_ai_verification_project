#!/usr/bin/env python3
"""Dependency-free, loopback-only UI for the repository's native Lean ciphers."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import webbrowser

ROOT = Path(__file__).resolve().parent.parent
STATIC = ROOT / "Web" / "static"
BINARY = ROOT / ".lake" / "build" / "bin" / ("crypto_web.exe" if os.name == "nt" else "crypto_web")
MAX_MESSAGE = 65536
MAX_REQUEST = 1024 * 1024
WORKERS = threading.BoundedSemaphore(4)


def transform(data):
    if not isinstance(data, dict):
        raise ValueError("Expected a JSON object.")
    for name in ("cipher", "operation", "key", "message"):
        if not isinstance(data.get(name), str):
            raise ValueError(f"{name.capitalize()} must be text.")
    cipher, operation = data["cipher"], data["operation"]
    if cipher not in ("chacha20", "chacha20-poly1305", "vigenere") or operation not in ("encrypt", "decrypt"):
        raise ValueError("Choose a supported cipher and operation.")
    if len(data["message"].encode("utf-8")) > MAX_MESSAGE * (2 if cipher != "vigenere" and operation == "decrypt" else 1):
        raise ValueError("Messages are limited to 64 KiB.")
    request = {name: data[name] for name in ("cipher", "operation", "key", "message")}
    if cipher != "vigenere":
        if not re.fullmatch(r"[0-9a-fA-F]{64}", data["key"]):
            raise ValueError("Enter a 32-byte key: exactly 64 hexadecimal digits.")
        nonce = data.get("nonce")
        if not isinstance(nonce, str) or not re.fullmatch(r"[0-9a-fA-F]{24}", nonce):
            raise ValueError("Enter a 12-byte nonce: exactly 24 hexadecimal digits.")
        request["nonce"] = nonce
        if operation == "encrypt":
            request["message"] = data["message"].encode("utf-8").hex()
        elif not re.fullmatch(r"(?:[0-9a-fA-F]{2})*", data["message"]):
            raise ValueError("Ciphertext must contain complete hexadecimal byte pairs.")
        if cipher == "chacha20-poly1305":
            aad = data.get("aad", "")
            aad_encoding = data.get("aad_encoding", "text")
            if not isinstance(aad, str) or aad_encoding not in ("text", "hex"):
                raise ValueError("Associated data must be text with text or hex encoding.")
            if aad_encoding == "hex":
                if len(aad) > MAX_MESSAGE * 2 or not re.fullmatch(r"(?:[0-9a-fA-F]{2})*", aad):
                    raise ValueError("Associated data must contain hex byte pairs, up to 64 KiB.")
                request["aad"] = aad
            else:
                raw_aad = aad.encode("utf-8")
                if len(raw_aad) > MAX_MESSAGE:
                    raise ValueError("Associated data is limited to 64 KiB.")
                request["aad"] = raw_aad.hex()
            if operation == "decrypt":
                tag = data.get("tag")
                if not isinstance(tag, str) or not re.fullmatch(r"[0-9a-fA-F]{32}", tag):
                    raise ValueError("Enter a 16-byte authentication tag: exactly 32 hexadecimal digits.")
                request["tag"] = tag
    else:
        if not re.fullmatch(r"[A-Za-z]{1,4096}", data["key"]):
            raise ValueError("Enter a Vigenère key of 1–4096 letters, A–Z only.")
    with WORKERS:
        completed = subprocess.run(
            [str(BINARY)], input=json.dumps(request, ensure_ascii=True) + "\n",
            text=True, encoding="utf-8", capture_output=True, timeout=15, cwd=ROOT,
        )
    if completed.returncode:
        raise RuntimeError("The Lean cipher process failed.")
    response = json.loads(completed.stdout)
    if "error" in response:
        raise ValueError(response["error"])
    if cipher != "vigenere" and operation == "decrypt":
        raw = bytes.fromhex(response["result"])
        response["hex"] = raw.hex()
        try:
            response["result"] = raw.decode("utf-8")
        except UnicodeDecodeError:
            response["result"] = raw.hex()
            response["encoding"] = "hex"
            response["notice"] = ("Authentication succeeded. The decrypted bytes are not UTF-8 text; showing hex."
                                  if cipher == "chacha20-poly1305" else
                                  "The decrypted bytes are not UTF-8 text; showing hex. Check your key and nonce.")
        else:
            response["encoding"] = "text"
    else:
        response["encoding"] = "text" if cipher == "vigenere" else "hex"
    return response


class Handler(BaseHTTPRequestHandler):
    # Avoid writing requests or secrets to access logs.
    def log_message(self, *args):
        pass

    def respond(self, status, body, content_type="application/json; charset=utf-8"):
        if isinstance(body, dict):
            body = json.dumps(body).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; connect-src 'self'; img-src 'self' data:; object-src 'none'; frame-ancestors 'none'; base-uri 'none'; form-action 'none'")
        self.end_headers()
        self.wfile.write(body)

    def allowed(self):
        port = self.server.server_address[1]
        hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
        # Reject DNS rebinding and requests initiated by unrelated websites.
        return (self.headers.get("Host") in hosts
                and self.headers.get("Origin") in (None, *(f"http://{host}" for host in hosts))
                and self.headers.get("Sec-Fetch-Site") not in ("cross-site", "same-site"))

    def do_GET(self):
        if not self.allowed():
            return self.respond(403, {"error": "Only local app requests are accepted."})
        routes = {"/": ("index.html", "text/html; charset=utf-8"),
                  "/app.js": ("app.js", "text/javascript; charset=utf-8"),
                  "/style.css": ("style.css", "text/css; charset=utf-8")}
        route = routes.get(self.path.split("?", 1)[0])
        if not route:
            return self.respond(404, {"error": "Not found."})
        self.respond(200, (STATIC / route[0]).read_bytes(), route[1])

    def do_POST(self):
        if not self.allowed():
            return self.respond(403, {"error": "Only local app requests are accepted."})
        if self.path != "/api/transform":
            return self.respond(404, {"error": "Not found."})
        if self.headers.get("Content-Type", "").split(";", 1)[0] != "application/json":
            return self.respond(415, {"error": "Send application/json."})
        try:
            size = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            return self.respond(400, {"error": "Invalid request length."})
        if size <= 0 or size > MAX_REQUEST:
            return self.respond(413, {"error": "Request is empty or too large."})
        self.connection.settimeout(15)
        try:
            data = json.loads(self.rfile.read(size))
            result = transform(data)
        except (ValueError, UnicodeError) as error:
            return self.respond(400, {"error": str(error)})
        except (subprocess.TimeoutExpired, TimeoutError):
            return self.respond(504, {"error": "The operation timed out. Try a smaller message."})
        except (OSError, RuntimeError):
            return self.respond(500, {"error": "Could not run the Lean cipher. Restart the app to rebuild it."})
        self.respond(200, result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8000)
    parser.add_argument("--no-browser", action="store_true")
    args = parser.parse_args()
    if not 0 <= args.port <= 65535:
        parser.error("port must be between 0 and 65535")
    lake = shutil.which("lake")
    if not lake:
        candidate = Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
        if candidate.is_file():
            lake = str(candidate)
    if not lake:
        parser.exit(1, "Lean/Lake is required. Install elan, then rerun this command.\n")
    print("Building the Lean ciphers and checking their correctness modules…", flush=True)
    try:
        subprocess.run([lake, "build", "crypto_web", "Crypto.Classical.Vigenere.Correctness",
                        "Crypto.Stream.ChaCha20.Correctness",
                        "Crypto.AEAD.ChaCha20Poly1305.Correctness"], cwd=ROOT, check=True)
    except subprocess.CalledProcessError:
        parser.exit(1, "Lean build failed; the web app was not started.\n")
    try:
        server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    except OSError as error:
        parser.exit(1, f"Cannot start the local app: {error}. Try --port 8001.\n")
    url = f"http://127.0.0.1:{server.server_address[1]}"
    print(f"\nCipher Studio is ready: {url}\nPress Ctrl+C to stop.\n", flush=True)
    if not args.no_browser:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped Cipher Studio.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
