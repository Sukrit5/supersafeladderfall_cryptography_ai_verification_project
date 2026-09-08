import Crypto.AEAD.ChaCha20Poly1305.Impl
import Crypto.AEAD.ChaCha20Poly1305.Archive.OriginalPoly1305
import Crypto.AEAD.ChaCha20Poly1305.Fast
import Crypto.AEAD.ChaCha20Poly1305.WordBlocks
import Crypto.AEAD.ChaCha20Poly1305.Machine

namespace Bench.Poly1305

def benchKey : List UInt8 :=
  (List.range 32).map fun i => ((i * 29 + 71) % 256).toUInt8

def makeMessage (size : Nat) : List UInt8 :=
  (List.range size).map fun i => ((i * 31 + i / 7 + 17) % 256).toUInt8

def checksum (bytes : List UInt8) : UInt64 :=
  bytes.foldl (fun acc b => acc * 1099511628211 + b.toUInt64) 14695981039346656037

inductive Version where
  | original
  | uint64
  | wordBlocks
  | machine
  | machineArray
  | wordAuth
  | machineAuth

def benchKeyArray : Array UInt8 := benchKey.toArray
def benchAAD : Array UInt8 := (List.range 12).toArray.map Nat.toUInt8

def run : Version → List UInt8 → Array UInt8 → List UInt8
  | .original, msg, _ => Crypto.ChaCha20Poly1305.Archive.Original.poly1305 msg benchKey
  | .uint64, msg, _ => Crypto.ChaCha20Poly1305.Fast.poly1305 msg benchKey
  | .wordBlocks, msg, _ => Crypto.ChaCha20Poly1305.WordBlocks.poly1305 msg benchKey
  | .machine, msg, _ => Crypto.ChaCha20Poly1305.Machine.poly1305 msg benchKey
  | .machineArray, _, arr => Crypto.ChaCha20Poly1305.Machine.poly1305Array arr benchKeyArray
  | .wordAuth, _, arr => Crypto.ChaCha20Poly1305.WordBlocks.poly1305
      (Crypto.ChaCha20Poly1305.encodeMacData benchAAD arr) benchKey
  | .machineAuth, _, arr => Crypto.ChaCha20Poly1305.authenticate benchAAD arr benchKey

def versionName : Version → String
  | .original => "original_full_nat"
  | .uint64 => "uint64_limbs"
  | .wordBlocks => "word_blocks"
  | .machine => "machine_list"
  | .machineArray => "machine_array"
  | .wordAuth => "word_auth"
  | .machineAuth => "machine_auth"

def timeN (version : Version) (count : Nat) (msg : List UInt8) : IO (Nat × UInt64) := do
  let arr := msg.toArray
  let sink ← IO.mkRef (0 : UInt64)
  let start ← IO.monoNanosNow
  let mut digest : UInt64 := 0
  for i in [0:count] do
    let tag := run version msg arr
    digest := digest * 1099511628211 + checksum tag + i.toUInt64
  sink.set digest
  let stop ← IO.monoNanosNow
  pure (stop - start, ← sink.get)

partial def calibrate (version : Version) (msg : List UInt8) (count : Nat := 1) : IO Nat := do
  let (elapsed, _) ← timeN version count msg
  if elapsed >= 40_000_000 || count >= 16384 then pure count
  else calibrate version msg (count * 2)

def sizes : List Nat := [0, 15, 16, 17, 64, 256, 1024, 4096, 16384]
def trials : Nat := 9

def benchmark (authOnly : Bool := false) : IO UInt32 := do
  IO.println "version,size_bytes,trial,iterations,elapsed_ns,ns_per_call,mb_per_second,checksum"
  for size in sizes do
    let msg := makeMessage size
    let arr := msg.toArray
    let oldTag := run .original msg arr
    if run .uint64 msg arr != oldTag then
      IO.eprintln s!"uint64 correctness mismatch at {size} bytes"
      return 1
    if run .wordBlocks msg arr != oldTag then
      IO.eprintln s!"word-block correctness mismatch at {size} bytes"
      return 1
    if run .machine msg arr != oldTag || run .machineArray msg arr != oldTag then
      IO.eprintln s!"machine correctness mismatch at {size} bytes"
      return 1
    if run .wordAuth msg arr != run .machineAuth msg arr then
      IO.eprintln s!"authentication correctness mismatch at {size} bytes"
      return 1
    let versions : List Version := if authOnly then [.wordAuth, .machineAuth]
      else [.original, .uint64, .wordBlocks, .machine, .machineArray]
    let configs ← versions.mapM fun version => do
      let iterations ← calibrate version msg
      discard <| timeN version iterations msg
      discard <| timeN version iterations msg
      pure (version, iterations)
    for trial in [0:trials] do
      for (version, iterations) in (if trial % 2 = 0 then configs else configs.reverse) do
        let (elapsed, digest) ← timeN version iterations msg
        let nsPerCall := elapsed.toFloat / iterations.toFloat
        let mbPerSecond := size.toFloat * 1000.0 / nsPerCall
        IO.println s!"{versionName version},{size},{trial + 1},{iterations},{elapsed},{nsPerCall},{mbPerSecond},{digest}"
  pure 0

end Bench.Poly1305

def main (args : List String) : IO UInt32 := Bench.Poly1305.benchmark (args.contains "auth")
