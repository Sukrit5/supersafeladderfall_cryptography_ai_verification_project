# Lean Crypto · Cipher Studio

A cryptography library with Lean 4 proofs that its implementations match
inspectable specifications, and a local web app for trying ChaCha20-Poly1305,
ChaCha20, and Vigenère.

## Run the local web app

Install **Python 3.9+** and **Lean via [elan](https://github.com/leanprover/elan)**.
The repository's `lean-toolchain` pins the required Lean version; elan downloads
it on first use if necessary. No Python packages or Node.js installation are needed.

From the downloaded repository, run:

```bash
python3 Web/server.py
```

The command builds the native Lean adapter, checks all three ciphers' correctness
modules, starts **http://127.0.0.1:8000**, and opens your browser. The first build
may take a little while. Stop it with **Ctrl+C**. If the port is occupied, use
`python3 Web/server.py --port 8001`; add `--no-browser` to open the URL yourself.
The command also works from another directory when given the full script path.

### Using the workbench

- **ChaCha20-Poly1305 (default):** authenticated encryption using the same
  key and nonce formats as ChaCha20. Optional associated data can be UTF-8 text
  or hex bytes; it is authenticated but not encrypted. Encryption produces
  hexadecimal ciphertext and a 16-byte authentication tag. Decryption requires
  that tag and exactly the same associated data, key, and nonce. A failed
  authentication returns an error with no plaintext. Downloads include the
  ciphertext, nonce, tag, associated data, and its encoding, but never the key.
  **Decrypt this result** transfers all these inputs automatically.
- **ChaCha20:** enter text and a 32-byte key (64 hexadecimal digits), or click
  **Generate key**. A fresh 12-byte nonce is generated for every encryption by
  default. Ciphertext is hexadecimal; save the key and nonce to decrypt it.
  The initial block counter is 1, matching the existing Lean API. To use a
  known nonce, uncheck **Fresh nonce each time**. Never reuse a nonce with the
  same key. This is raw ChaCha20, without authentication or wrong-key detection.
- **Vigenère:** enter a nonempty A–Z key, such as `LEMON`. The message is
  converted to uppercase A–Z letters and all other characters are removed,
  matching `Crypto.String.toAlphabets`. The app previews this normalization.
  **Load example** produces `ATTACKATDAWN + LEMON = LXFOPVEFRNHR`.
  Vigenère is a historical learning tool, not secure encryption.
- Both modes support decryption, copying results, and downloading them.
  Encryption downloads include the ciphertext and nonce (where applicable), **not the key**.
  **Decrypt this result** prepares a roundtrip using the same key and nonce.
  ChaCha20 and AEAD decryption display hex if the recovered bytes are not valid UTF-8.
  Messages are limited to 64 KiB (before hexadecimal encoding).

### How it connects to Lean

`Web/static/` contains the frontend, and `Web/server.py` serves it on loopback
only. Each operation sends JSON over standard input to `.lake/build/bin/crypto_web`,
whose adapter in `Web/Main.lean` calls the repository's existing cipher functions.
AEAD calls `Crypto.ChaCha20Poly1305.sealPacket` and
`Crypto.ChaCha20Poly1305.open?` directly; the latter authenticates before
returning any plaintext. There is no JavaScript or Python reimplementation of any cipher, and secret
keys are not placed in process arguments. The app uses no external assets,
cloud API, browser storage, or request logging.

The existing proofs establish Lean implementation/specification equivalence.
The web adapter, HTTP server, text/hex conversions, and native compilation are
outside that proof boundary. No constant-time guarantee is claimed.

## Build and test

```bash
lake build
lake build Crypto.Classical.Vigenere.Tests Crypto.Stream.ChaCha20.Tests
lake build Crypto.AEAD.ChaCha20Poly1305.Tests
lake build crypto_web
python3 -m unittest discover -s Web -p 'test_*.py' -v
```

The web integration tests exercise the native Lean binary, including the RFC
8439 encryption and AEAD vectors, Vigenère's known vector, Unicode and multiblock
roundtrips, AEAD rejection of altered ciphertext, tags, keys, nonces, and
associated data, input validation, and local HTTP access restrictions.

Specifications and proofs live in `Crypto/Classical/Vigenere/`,
`Crypto/Stream/ChaCha20/`, and `Crypto/AEAD/ChaCha20Poly1305/`.
The frontend exposes all three ciphers.
