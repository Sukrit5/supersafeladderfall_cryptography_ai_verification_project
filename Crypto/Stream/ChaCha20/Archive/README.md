# Archived ChaCha20 implementation

This directory preserves the implementation and proof from commit `1db9807`
before the block-oriented encryption optimization.

- `OriginalImpl.lean` contains the original implementation.
- `OriginalCorrectness.lean` contains its original correctness proof, with only
  its implementation import redirected to `OriginalImpl.lean`.

The archived and current implementations intentionally retain the same
`Crypto.ChaCha20` namespace and public API. They must therefore be compiled in
separate executable targets rather than imported into one Lean module.

`PrecomputedImpl.lean` and `PrecomputedCorrectness.lean` preserve the next
revision, which precomputes each message keystream block once. This is the
baseline for the raw-array round-loop optimization in the current module.

```bash
lake build Crypto.Stream.ChaCha20.Archive.PrecomputedCorrectness
lake build chacha20_bench_precomputed
.lake/build/bin/chacha20_bench_precomputed precomputed
```

`RawRoundsImpl.lean` and `RawRoundsCorrectness.lean` preserve the raw-array
round-loop revision immediately before quarter-round arithmetic was fused into
the next optimization. The retained optimization uses proof-bounded keystream
table access instead of defaulting `get!` lookups.

```bash
lake build Crypto.Stream.ChaCha20.Archive.RawRoundsCorrectness
lake build chacha20_bench_raw_rounds
.lake/build/bin/chacha20_bench_raw_rounds raw-rounds
```

```bash
lake build Crypto.Stream.ChaCha20.Archive.OriginalCorrectness
lake build chacha20_bench_original
.lake/build/bin/chacha20_bench_original original
```
