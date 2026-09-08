# AI-authored optimization log

Date: 2026-09-05

> This file was written by me, Codex, the AI assistant in this conversation.
> Its contents are **not to be trusted without independent verification**,
> except for the fact that performance has improved according to the saved
> benchmarks. That exception concerns the measured workloads and conditions
> only; it is not a guarantee of performance elsewhere. Descriptions of changes,
> explanations, and correctness or security claims below require verification.

## Scope and attribution

This records the Poly1305 optimizations I made during this conversation and
their supporting proof, test, and benchmark work. It is not a history of every
optimization in this repository. The existing `Fast` implementation's UInt64
multiplication and carry arithmetic, its correctness development, and earlier
ChaCha20/Vigenère optimizations predated this work; I do not claim authorship
of them. The benchmark harness also existed before I extended it.

The intended invariant throughout both rounds was to retain the exact same
[Spec.lean](Crypto/AEAD/ChaCha20Poly1305/Spec.lean), particularly
`Crypto.ChaCha20Poly1305.Spec.poly1305`, rather than introduce an easier or
different specification. No changes to that file were made in these rounds.

## Round 1: full-block decoding and tag serialization

Implementation: [WordBlocks.lean](Crypto/AEAD/ChaCha20Poly1305/WordBlocks.lean).
Proofs: [WordBlocksCorrectness.lean](Crypto/AEAD/ChaCha20Poly1305/WordBlocksCorrectness.lean).

1. **Decode full 16-byte blocks directly into UInt64 limbs.** `pack4` packs
   four little-endian bytes; `addWords` splits four such words into five
   radix-2^26 limbs and adds the implicit block bit. This bypasses full-block
   large-`Nat` construction and subsequent decomposition.
2. **Consume full blocks directly from the list.** `blocks` pattern-matches
   16 bytes without constructing a temporary `take 16` chunk list. It reuses
   the existing `Fast.mulReduce` arithmetic. The final short block retains
   the reference decoder.
3. **Serialize the tag with word shifts.** `tagBytes` uses two UInt64 words
   to emit the low 128 bits, replacing repeated large-`Nat` division/powers
   in serialization. Key setup and final modular arithmetic still used `Nat`
   at this stage.
4. **Connect the implementation to the existing public API and theorem.**
   `WordBlocks.poly1305_correct` targets the unchanged specification;
   `blocks_eq` establishes exact equality with the reference block loop,
   including arbitrary initial limb states. This version remains available
   as the baseline for round 2.

## Round 2: key setup, finalization, and array integration

Implementation: [Machine.lean](Crypto/AEAD/ChaCha20Poly1305/Machine.lean).
Proofs: [MachineCorrectness.lean](Crypto/AEAD/ChaCha20Poly1305/MachineCorrectness.lean)
and [MachineArrayCorrectness.lean](Crypto/AEAD/ChaCha20Poly1305/MachineArrayCorrectness.lean).

1. **Load and clamp the key using machine words.** `loadWords` performs
   zero-extended byte loads; `decodeWords` applies the clamp directly to the
   radix-2^26 limbs. The pad is loaded as four 32-bit-valued UInt64 words.
   This removes large-`Nat` key decoding and clamping from the active path,
   while retaining the specification's behavior for arbitrary key lengths.
2. **Finalize using bounded word arithmetic.** `finish` propagates carries,
   computes the small correction for reduction modulo 2^130 − 5, repacks into
   radix-2^32 words, adds the pad with carries, and serializes the low 128 bits.
   Supporting proofs relate this to the reference modular arithmetic and
   establish bounds needed to avoid unintended UInt64 overflow. Runtime key
   setup and finalization no longer construct large natural numbers.
3. **Add a direct array block loop.** `blocksArray` reads full blocks from
   the input array without converting the whole message to a list. Only the
   remaining tail, at most 15 bytes, is extracted and passed to the reference
   decoder. It reads the array; it does not mutate it.
4. **Expose both optimized APIs.** Public `poly1305` now uses
   `Machine.poly1305`, and `poly1305Array` uses `Machine.poly1305Array`.
   The list API retains list traversal but benefits from word-based setup
   and finalization; the array API additionally uses direct indexed loads.
5. **Keep AEAD's MAC data in arrays.** `encodeMacDataArray` constructs the
   padded AAD, ciphertext, and length fields as arrays. `authenticate` feeds
   that buffer to the array Poly1305 API; `sealPacket` and `open?` use this
   route. This avoids the previous whole-buffer list representation, but
   still allocates a combined MAC buffer: it is not streaming authentication.
6. **Preserve the existing public correctness statements.** The proof bodies
   now use the machine implementation's refinement theorems. New
   `poly1305Array_correct`, `encodeMacDataArray_correct`, and
   `authenticate_correct` connect the array API and MAC layout to the same
   specification and previous list contract.

Public integration is in [Impl.lean](Crypto/AEAD/ChaCha20Poly1305/Impl.lean)
and [Correctness.lean](Crypto/AEAD/ChaCha20Poly1305/Correctness.lean).
These changes use newly proved `Machine` routines, not the previously unused
`Fast.decodeR`, `Fast.blocks`, or `Fast.finish` prototypes.

## Supporting validation and measurement changes

- Extended [Tests.lean](Crypto/AEAD/ChaCha20Poly1305/Tests.lean) to compare the
  implementations against the specification on lengths 0–257 with zero,
  all-one, and patterned data; selected arbitrary key-length boundaries;
  serialization boundaries; and finalization states near the modulus and
  with large carries. Added array MAC-layout and AEAD boundary checks for
  81 size pairs, alongside RFC vectors, roundtrips, and rejection tests.
- Changed runtime test failures from printed messages to thrown errors, so
  mismatches fail the build.
- Extended [Poly1305.lean](Bench/Poly1305.lean) to retain and compare the
  historical baselines, machine list/array APIs, and old/new authentication
  paths. Added pre-timing output agreement checks and a rolling checksum
  instead of an XOR accumulator that could cancel to zero.
- Used two warmups, nine trials per run, per-version calibration toward
  40 ms with a 16,384-iteration cap, and interleaved/reversed version order.
  Timed results pass through an `IO.Ref` before the ending clock read.
- Extended [plot_results.py](Bench/plot_results.py) with selectable versions,
  labels, and captions, and added three comparison graphs. Full tables,
  raw-data links, methodology, and graph commands are in
  [Bench/README.md](Bench/README.md).

These are validation/measurement changes, not additional cryptographic
algorithm speedups. The arithmetic multiplication kernel was not replaced.

## Saved benchmark improvements

Measurements were local native Lean 4.32.2 runs on macOS arm64. Values below
are median microseconds per call, pooling two runs with nine samples each.
Each row identifies its actual baseline; results from different rounds should
not be multiplied into a claimed aggregate speedup.

| Comparison | Bytes | Baseline µs | New µs | Observed speedup |
|---|---:|---:|---:|---:|
| Round 1: Fast → WordBlocks | 16 | 10.078 | 5.062 | 1.99× |
| Round 1: Fast → WordBlocks | 1024 | 158.245 | 6.745 | 23.46× |
| Round 1: Fast → WordBlocks | 16384 | 2399.880 | 31.305 | 76.66× |
| Round 2: WordBlocks → Machine list | 16 | 5.159 | 0.332 | ≈15.5× |
| Round 2: WordBlocks → Machine list | 16384 | 32.615 | 27.644 | ≈1.18× |
| Round 2: WordBlocks → Machine array | 16384 | 32.615 | 13.813 | ≈2.36× |
| Authentication: list buffer/WordBlocks → array buffer/Machine | 16 | 6.790 | 1.626 | 4.17× |
| Authentication: list buffer/WordBlocks → array buffer/Machine | 16384 | 238.400 | 40.666 | 5.86× |

Evidence by round:

- Round 1: [run 1](Bench/poly1305-word-blocks.csv),
  [run 2](Bench/poly1305-word-blocks-repeat.csv),
  [graph](Bench/04-poly1305-uint64-vs-word-blocks.svg).
- Round 2 standalone: [run 1](Bench/poly1305-machine.csv),
  [run 2](Bench/poly1305-machine-repeat.csv),
  [list API graph](Bench/05-poly1305-word-blocks-vs-machine-list.svg).
- Authentication: [run 1](Bench/poly1305-auth.csv),
  [run 2](Bench/poly1305-auth-repeat.csv),
  [graph](Bench/06-poly1305-auth-word-vs-machine.svg).

Standalone tests use preconstructed messages, one deterministic key and data
pattern, and include key setup, tag allocation, and checksum overhead. The
array API receives a prepared key array; list API timings include their key
conversion/setup. Authentication measurements include MAC-buffer construction
with fixed 12-byte AAD, but exclude ChaCha20 encryption and one-time-key
derivation. They are not end-to-end AEAD or production-library comparisons.

## Verification record and limits

Before this documentation-only addition, the implementation work completed:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build Crypto.AEAD.ChaCha20Poly1305.Tests crypto
```

The build and regression checks passed. Axiom inspections of
`poly1305_correct`, `poly1305Array_correct`, `seal_correct`, `open_correct`,
and `open_seal` reported only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx` or newly introduced axioms. The specification diff was empty.
These are my reports of checks, not substitutes for independent verification.
Recheck the source, theorem statements, proof dependencies, and build locally.
The benchmark executable can be rebuilt with `lake build poly1305_bench`;
the reproduction commands are in the benchmark README. Preserve the saved
historical CSVs when collecting new measurements.

Functional agreement with the specification does not establish constant-time
execution, side-channel resistance, compiler correctness, or the adequacy of
the specification itself. Message indices/lengths remain `Nat`, and partial
blocks still use the reference decoder. Previously identified concerns about
counter wrap and tag comparison were not fixed by these optimizations.
Performance measurements alone are not evidence of cryptographic security.
