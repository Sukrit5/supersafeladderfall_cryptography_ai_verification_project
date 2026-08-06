/-
  Crypto.Stream.ChaCha20.Spec

  CHACHA20 CIPHER SPECIFICATION (RFC 8439)
  ========================================
  Minimal mathematical definition. THIS IS ALL YOU NEED TO INSPECT.

  ChaCha20 is a stream cipher with:
    - 256-bit key (8 × 32-bit words)
    - 96-bit nonce (3 × 32-bit words)
    - 32-bit counter
    - 64-byte keystream blocks

  Core operation: Quarter Round (QR)
    a += b; d ^= a; d <<<= 16
    c += d; b ^= c; b <<<= 12
    a += b; d ^= a; d <<<= 8
    c += d; b ^= c; b <<<= 7

  Block function: 10 double rounds (column + diagonal) + add initial state
  Encryption: XOR plaintext with keystream
-/

namespace Crypto.ChaCha20.Spec

/-! ## THE ENTIRE SPECIFICATION -/

/-- 32-bit word (the basic unit of ChaCha20) -/
abbrev Word := UInt32

/-- ChaCha20 state: 16 × 32-bit words -/
abbrev State := Fin 16 → Word

/-- ChaCha20 key: 8 × 32-bit words (256 bits) -/
abbrev Key := Fin 8 → Word

/-- ChaCha20 nonce: 3 × 32-bit words (96 bits) -/
abbrev Nonce := Fin 3 → Word

/-- ChaCha20 counter: 32-bit -/
abbrev Counter := Word

/-! ### Constants: "expand 32-byte k" in little-endian -/

def const0 : Word := 0x61707865  -- "expa"
def const1 : Word := 0x3320646e  -- "nd 3"
def const2 : Word := 0x79622d32  -- "2-by"
def const3 : Word := 0x6b206574  -- "te k"

/-! ### Rotate left operation for UInt32

  ROTL(x, n) = (x << n) | (x >> (32 - n))
-/

/-- Rotate left by n bits (0 ≤ n ≤ 32) -/
@[inline]
def rotl (x : Word) (n : UInt32) : Word :=
  (x <<< n) ||| (x >>> (32 - n))

/-! ### Quarter Round: The core primitive

  This is the heart of ChaCha20. Each operation is:
  - ADD (modular addition)
  - XOR
  - ROTL (rotate left)
-/

/-- Quarter round on 4 words: the complete ChaCha20 primitive -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  -- Step 1: a += b; d ^= a; d <<<= 16
  let a := a + b
  let d := rotl (d ^^^ a) 16
  -- Step 2: c += d; b ^= c; b <<<= 12
  let c := c + d
  let b := rotl (b ^^^ c) 12
  -- Step 3: a += b; d ^= a; d <<<= 8
  let a := a + b
  let d := rotl (d ^^^ a) 8
  -- Step 4: c += d; b ^= c; b <<<= 7
  let c := c + d
  let b := rotl (b ^^^ c) 7
  (a, b, c, d)

/-! ### State initialization

  State layout (16 words):
  ┌───────┬───────┬───────┬───────┐
  │const0 │const1 │const2 │const3 │  [0-3]   Constants
  ├───────┼───────┼───────┼───────┤
  │ key0  │ key1  │ key2  │ key3  │  [4-7]   Key (first half)
  ├───────┼───────┼───────┼───────┤
  │ key4  │ key5  │ key6  │ key7  │  [8-11]  Key (second half)
  ├───────┼───────┼───────┼───────┤
  │counter│nonce0 │nonce1 │nonce2 │  [12-15] Counter + Nonce
  └───────┴───────┴───────┴───────┘
-/

/-- Initialize state from key, counter, and nonce -/
def initState (key : Key) (counter : Counter) (nonce : Nonce) : State := fun i =>
  if i.val = 0 then const0
  else if i.val = 1 then const1
  else if i.val = 2 then const2
  else if i.val = 3 then const3
  else if i.val = 4 then key ⟨0, by omega⟩
  else if i.val = 5 then key ⟨1, by omega⟩
  else if i.val = 6 then key ⟨2, by omega⟩
  else if i.val = 7 then key ⟨3, by omega⟩
  else if i.val = 8 then key ⟨4, by omega⟩
  else if i.val = 9 then key ⟨5, by omega⟩
  else if i.val = 10 then key ⟨6, by omega⟩
  else if i.val = 11 then key ⟨7, by omega⟩
  else if i.val = 12 then counter
  else if i.val = 13 then nonce ⟨0, by omega⟩
  else if i.val = 14 then nonce ⟨1, by omega⟩
  else nonce ⟨2, by omega⟩  -- i.val = 15

/-! ### Apply quarter round to state at indices (a, b, c, d) -/

/-- Apply quarter round to 4 positions in state -/
def applyQR (s : State) (ai bi ci di : Fin 16) : State :=
  let (a', b', c', d') := quarterRound (s ai) (s bi) (s ci) (s di)
  fun i =>
    if i = ai then a'
    else if i = bi then b'
    else if i = ci then c'
    else if i = di then d'
    else s i

/-! ### Double round: column round + diagonal round

  Column round indices:
    QR(0, 4,  8, 12), QR(1, 5,  9, 13), QR(2, 6, 10, 14), QR(3, 7, 11, 15)

  Diagonal round indices:
    QR(0, 5, 10, 15), QR(1, 6, 11, 12), QR(2, 7,  8, 13), QR(3, 4,  9, 14)
-/

/-- Column round: QR on each column -/
def columnRound (s : State) : State :=
  let s := applyQR s ⟨0, by omega⟩ ⟨4, by omega⟩ ⟨8, by omega⟩  ⟨12, by omega⟩
  let s := applyQR s ⟨1, by omega⟩ ⟨5, by omega⟩ ⟨9, by omega⟩  ⟨13, by omega⟩
  let s := applyQR s ⟨2, by omega⟩ ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨14, by omega⟩
  let s := applyQR s ⟨3, by omega⟩ ⟨7, by omega⟩ ⟨11, by omega⟩ ⟨15, by omega⟩
  s

/-- Diagonal round: QR on each diagonal -/
def diagonalRound (s : State) : State :=
  let s := applyQR s ⟨0, by omega⟩ ⟨5, by omega⟩ ⟨10, by omega⟩ ⟨15, by omega⟩
  let s := applyQR s ⟨1, by omega⟩ ⟨6, by omega⟩ ⟨11, by omega⟩ ⟨12, by omega⟩
  let s := applyQR s ⟨2, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩  ⟨13, by omega⟩
  let s := applyQR s ⟨3, by omega⟩ ⟨4, by omega⟩ ⟨9, by omega⟩  ⟨14, by omega⟩
  s

/-- Double round = column round followed by diagonal round -/
def doubleRound (s : State) : State :=
  diagonalRound (columnRound s)

/-! ### Block function: 10 double rounds + add initial state -/

/-- Apply n double rounds -/
def nRounds (n : Nat) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 => nRounds n (doubleRound s)

/-- Add two states element-wise -/
def addStates (s1 s2 : State) : State := fun i => s1 i + s2 i

/-- ChaCha20 block function: 20 rounds (10 double rounds) + add initial state -/
def block (key : Key) (counter : Counter) (nonce : Nonce) : State :=
  let initial := initState key counter nonce
  let final := nRounds 10 initial
  addStates final initial

/-! ### Keystream generation and encryption -/

/-- Serialize state to 64 bytes (little-endian) -/
def stateToBytes (s : State) : Fin 64 → UInt8 := fun i =>
  let wordIdx : Fin 16 := ⟨i.val / 4, by omega⟩
  let byteIdx := i.val % 4
  let word := s wordIdx
  -- Extract byte at position byteIdx (little-endian)
  (word >>> (byteIdx * 8).toUInt32).toUInt8

/-- Generate keystream byte at position pos -/
def keystreamByte (key : Key) (nonce : Nonce) (pos : Nat) : UInt8 :=
  let blockNum : Counter := (pos / 64).toUInt32
  let byteInBlock : Fin 64 := ⟨pos % 64, by omega⟩
  let blockState := block key blockNum nonce
  stateToBytes blockState byteInBlock

/-- Encrypt a single byte at position i -/
def encryptByte (key : Key) (nonce : Nonce) (plaintext : List UInt8) (i : Nat)
    (hi : i < plaintext.length) : UInt8 :=
  plaintext[i] ^^^ keystreamByte key nonce i

/-- Decrypt a single byte at position i (same as encrypt - XOR is self-inverse) -/
def decryptByte (key : Key) (nonce : Nonce) (ciphertext : List UInt8) (i : Nat)
    (hi : i < ciphertext.length) : UInt8 :=
  ciphertext[i] ^^^ keystreamByte key nonce i

/-! ## Spec properties -/

/-- XOR is self-inverse: encrypt and decrypt are the same operation -/
theorem decrypt_eq_encrypt (key : Key) (nonce : Nonce) (msg : List UInt8) (i : Nat)
    (hi : i < msg.length) :
    decryptByte key nonce msg i hi = encryptByte key nonce msg i hi := rfl

end Crypto.ChaCha20.Spec
