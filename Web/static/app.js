"use strict";
const $ = (id) => document.getElementById(id);
const encoder = new TextEncoder();
let operation = "encrypt";
let resultSnapshot = null;
let pending = false;
let revision = 0;
const cipher = () => document.querySelector('input[name="cipher"]:checked').value;
const randomHex = (length) => Array.from(crypto.getRandomValues(new Uint8Array(length)), b => b.toString(16).padStart(2, "0")).join("");
const announce = (text) => { $("announcement").textContent = text; };

function clearResult() {
  revision++;
  resultSnapshot = null;
  $("empty-state").hidden = false;
  $("result-content").hidden = true;
  $("result").textContent = "";
  $("result-nonce").textContent = "";
  $("result-tag").textContent = "";
  $("error").hidden = true;
  $("copy").textContent = "Copy result";
}

function updateCount() {
  const message = $("message").value;
  const classical = cipher() === "vigenere";
  const normalized = message.replace(/[^a-zA-Z]/g, "").toUpperCase();
  $("message-count").textContent = classical ? `${normalized.length.toLocaleString()} letters` : `${encoder.encode(message).length.toLocaleString()} ${operation === "decrypt" ? "hex characters" : "bytes"}`;
  $("normalized").hidden = !classical || !message;
  $("normalized").textContent = `Will process: ${normalized.slice(0, 180) || "(no A–Z letters)"}${normalized.length > 180 ? "…" : ""}`;
}

function updateUI() {
  const classical = cipher() === "vigenere";
  const aead = cipher() === "chacha20-poly1305";
  const decrypt = operation === "decrypt";
  $("encrypt-mode").setAttribute("aria-pressed", String(!decrypt));
  $("decrypt-mode").setAttribute("aria-pressed", String(decrypt));
  $("message-label").replaceChildren(Object.assign(document.createElement("span"), {textContent: "02"}), document.createTextNode(decrypt ? "Your ciphertext" : "Your message"));
  $("message").placeholder = decrypt ? (classical ? "Paste your encrypted letters…" : "Paste your hexadecimal ciphertext…") : "Enter your message…";
  $("message-help").textContent = classical ? "A–Z only. Other characters are removed; letters become uppercase." : decrypt ? "Paste hex byte pairs without spaces." : "Text is encoded as UTF-8. Maximum 64 KiB.";
  $("key").placeholder = classical ? "A word or phrase without spaces, e.g. LEMON" : "64 hexadecimal digits";
  $("key").maxLength = classical ? 4096 : 64;
  $("key-help").textContent = classical ? "A nonempty key containing letters A–Z. Lowercase is accepted." : "32 bytes · 64 hex digits. Save this key to decrypt your message.";
  $("generate-key").hidden = classical;
  $("nonce-group").hidden = classical;
  $("aad-group").hidden = !aead;
  $("tag-group").hidden = !aead || !decrypt;
  $("tag").required = aead && decrypt;
  $("aad").placeholder = $("aad-encoding").value === "hex" ? "Hex byte pairs, e.g. 50515253" : "e.g. message ID or document title";
  $("auto-nonce").parentElement.hidden = decrypt;
  $("nonce").readOnly = !decrypt && $("auto-nonce").checked;
  $("nonce").placeholder = decrypt || !$("auto-nonce").checked ? "24 hexadecimal digits" : "Generated when you encrypt";
  $("submit-label").textContent = pending ? "Computing…" : decrypt ? "Decrypt message" : "Encrypt message";
  $("output-badge").textContent = classical || decrypt ? "TEXT OUTPUT" : "HEX OUTPUT";
  $("info-heading").textContent = classical ? "ABOUT / VIGENÈRE" : "ABOUT / CHACHA20";
  $("info-copy").textContent = classical ? "Each letter shifts by a key letter. The key repeats across the message, with arithmetic modulo 26." : "A 256-bit key, a 96-bit nonce, and 20 rounds of addition, rotation, and XOR.";
  $("info-tags").replaceChildren(...(classical ? ["A–Z alphabet", "Repeating key", "Modulo 26"] : ["256-bit key", "Counter 1", "UTF-8 → hex"]).map(text => Object.assign(document.createElement("span"), {textContent: text})));
  $("scope-note").textContent = classical ? "A historical cipher for learning and exploration. Vigenère is not secure for sensitive messages." : "Raw ChaCha20 encrypts without authenticating the result. An incorrect key is not detected.";
  if (aead) {
    $("info-heading").textContent = "ABOUT / CHACHA20-POLY1305";
    $("info-copy").textContent = "ChaCha20 encrypts the message. Poly1305 authenticates the ciphertext and associated data before decryption releases any plaintext.";
    $("info-tags").replaceChildren(...["256-bit key", "128-bit tag", "AEAD"].map(text => Object.assign(document.createElement("span"), {textContent: text})));
    $("scope-note").textContent = "Decryption requires the original key, nonce, associated data, and tag. Authentication failure releases no plaintext.";
  }
  updateCount();
}

document.querySelectorAll('input[name="cipher"]').forEach(input => input.addEventListener("change", () => {
  clearResult();
  $("key").value = "";
  $("message").value = "";
  $("nonce").value = "";
  $("aad").value = "";
  $("tag").value = "";
  $("aad-encoding").value = "text";
  operation = "encrypt";
  $("auto-nonce").checked = true;
  updateUI();
}));
for (const mode of ["encrypt", "decrypt"]) $(mode + "-mode").addEventListener("click", () => {
  operation = mode;
  clearResult();
  updateUI();
});
for (const id of ["message", "key", "nonce", "aad", "tag"]) $(id).addEventListener("input", () => { clearResult(); updateCount(); });
$("aad-encoding").addEventListener("change", () => { clearResult(); updateUI(); });
$("auto-nonce").addEventListener("change", () => { clearResult(); updateUI(); });
$("generate-key").addEventListener("click", () => {
  clearResult();
  $("key").value = randomHex(32);
  announce("A new 32-byte key was generated. Save it to decrypt your result.");
});
$("example").addEventListener("click", () => {
  clearResult();
  operation = "encrypt";
  $("tag").value = "";
  $("aad").value = cipher() === "chacha20-poly1305" ? "Message ID: 001" : "";
  $("aad-encoding").value = "text";
  if (cipher() === "vigenere") {
    $("message").value = "ATTACK AT DAWN";
    $("key").value = "LEMON";
  } else {
    $("message").value = "Every secret starts with a message.";
    $("key").value = randomHex(32);
    $("auto-nonce").checked = true;
  }
  updateUI();
});

$("cipher-form").addEventListener("submit", async (event) => {
  event.preventDefault();
  if (pending) return;
  clearResult();
  const currentRevision = revision;
  const request = {cipher: cipher(), operation, key: $("key").value, message: $("message").value};
  if (request.cipher !== "vigenere") {
    if (operation === "encrypt" && $("auto-nonce").checked) $("nonce").value = randomHex(12);
    request.nonce = $("nonce").value;
  }
  if (request.cipher === "chacha20-poly1305") {
    request.aad = $("aad").value;
    request.aad_encoding = $("aad-encoding").value;
    if (operation === "decrypt") request.tag = $("tag").value;
  }
  pending = true;
  $("submit").disabled = true;
  $("cipher-form").setAttribute("aria-busy", "true");
  updateUI();
  try {
    const response = await fetch("/api/transform", {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(request),
    });
    const data = await response.json();
    if (!response.ok) throw new Error(data.error || "The cipher could not process this input.");
    if (currentRevision !== revision) return;
    resultSnapshot = {request, data};
    $("empty-state").hidden = true;
    $("result-content").hidden = false;
    $("result").textContent = data.result || "(empty result)";
    $("result-status").textContent = data.authenticated ? "Authenticated · decryption complete" : operation === "encrypt" ? "Encryption complete" : "Decryption complete";
    $("output-badge").textContent = data.encoding === "hex" ? "HEX OUTPUT" : "TEXT OUTPUT";
    $("result-size").textContent = `${(data.encoding === "hex" ? data.result.length / 2 : encoder.encode(data.result).length).toLocaleString()} bytes`;
    $("result-nonce-group").hidden = request.cipher === "vigenere";
    $("result-nonce").textContent = request.nonce || "";
    $("result-tag-group").hidden = !data.tag;
    $("result-tag").textContent = data.tag || "";
    $("packet-help").hidden = !data.tag;
    $("result-notice").hidden = !data.notice;
    $("result-notice").textContent = data.notice || "";
    $("reverse").hidden = operation !== "encrypt";
    announce(`${$("result-status").textContent}. Result is ready.`);
  } catch (error) {
    if (currentRevision !== revision) return;
    $("error").textContent = error instanceof TypeError ? "Cannot reach the local app. Check that the launch command is still running." : error.message;
    $("error").hidden = false;
  } finally {
    pending = false;
    $("submit").disabled = false;
    $("cipher-form").removeAttribute("aria-busy");
    // Preserve a non-UTF-8 result's hex label.
    $("submit-label").textContent = operation === "encrypt" ? "Encrypt message" : "Decrypt message";
  }
});

$("copy").addEventListener("click", async () => {
  if (!resultSnapshot) return;
  try {
    await navigator.clipboard.writeText(resultSnapshot.data.result);
    $("copy").textContent = "Copied ✓";
    announce("Result copied to clipboard.");
  } catch {
    announce("Clipboard unavailable. Select the result and copy it manually.");
    $("copy").textContent = "Select result to copy";
    $("result").focus();
    const range = document.createRange();
    range.selectNodeContents($("result"));
    const selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
  }
});
$("download").addEventListener("click", () => {
  if (!resultSnapshot) return;
  const {request, data} = resultSnapshot;
  // Export the nonce and ciphertext, never the secret key or input plaintext.
  const content = request.operation === "encrypt" ? JSON.stringify({cipher: request.cipher, encoding: data.encoding, ciphertext: data.result, ...(request.nonce ? {nonce: request.nonce, counter: 1} : {}), ...(data.tag ? {tag: data.tag, aad: request.aad, aad_encoding: request.aad_encoding} : {})}, null, 2) : data.result;
  const url = URL.createObjectURL(new Blob([content], {type: request.operation === "encrypt" ? "application/json" : "text/plain;charset=utf-8"}));
  const anchor = document.createElement("a");
  anchor.href = url;
  anchor.download = `${request.cipher}-${request.operation === "encrypt" ? "ciphertext.json" : "decrypted.txt"}`;
  anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
});
$("reverse").addEventListener("click", () => {
  if (!resultSnapshot) return;
  const {request, data} = resultSnapshot;
  operation = "decrypt";
  $("message").value = data.result;
  $("key").value = request.key;
  $("nonce").value = request.nonce || "";
  $("tag").value = data.tag || "";
  $("aad").value = request.aad || "";
  $("aad-encoding").value = request.aad_encoding || "text";
  clearResult();
  updateUI();
  $("submit").focus();
  announce("All decryption inputs are ready. Press Decrypt message.");
});
updateUI();
