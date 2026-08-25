import Crypto.Stream.ChaCha20.Archive.RawRoundsImpl

open Crypto.ChaCha20

def benchKey : Key :=
  ⟨#[0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
     0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], rfl⟩

def benchNonce : Nonce :=
  ⟨#[0x00000000, 0x4a000000, 0x00000000], rfl⟩

def makeMessage (size : Nat) : Array UInt8 :=
  Array.ofFn (n := size) fun i => ((i.val * 31 + 17) % 256).toUInt8

def checksum (bytes : Array UInt8) : UInt64 :=
  bytes.foldl (fun acc b => acc * 1099511628211 + b.toUInt64) 14695981039346656037

def timeN (count : Nat) (msg : Array UInt8) : IO (Nat × UInt64) := do
  let sink ← IO.mkRef (0 : UInt64)
  let start ← IO.monoNanosNow
  let mut digest : UInt64 := 0
  for i in [0:count] do
    let result := encrypt benchKey benchNonce msg
    let sample := if result.isEmpty then 0 else result[result.size - 1]!.toUInt64
    digest := digest ^^^ (sample + i.toUInt64)
  sink.set digest
  let stop ← IO.monoNanosNow
  let observed ← sink.get
  pure (stop - start, observed)

partial def calibrate (msg : Array UInt8) (count : Nat := 1) : IO Nat := do
  let (elapsed, _) ← timeN count msg
  if elapsed >= 30_000_000 || count >= 4096 then
    pure count
  else
    calibrate msg (count * 2)

def sizes : List Nat := [64, 256, 1024, 4096, 16384, 65536]

def trials : Nat := 9

def main (args : List String) : IO UInt32 := do
  let version := args.head?.getD "unknown"
  IO.println "version,size_bytes,trial,iterations,elapsed_ns,ns_per_call,checksum"
  for size in sizes do
    let msg := makeMessage size
    let iterations ← calibrate msg
    -- Warm up allocation and generated code paths outside the measured samples.
    discard <| timeN iterations msg
    discard <| timeN iterations msg
    for trial in [0:trials] do
      let (elapsed, _) ← timeN iterations msg
      let digest := checksum (encrypt benchKey benchNonce msg)
      let nsPerCall := elapsed.toFloat / iterations.toFloat
      IO.println s!"{version},{size},{trial + 1},{iterations},{elapsed},{nsPerCall},{digest}"
  pure 0
