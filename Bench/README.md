# ChaCha20 performance comparison

`ChaCha20.lean` is a revision-neutral native benchmark. It warms each input
size twice, calibrates samples toward 30 ms, and records nine trials. The timed
result is forced through an `IO.Ref` before the ending clock read.

`ChaCha20Original.lean` is the same harness with its import redirected to the
archived implementation. This allows both versions to remain benchmarkable
after the current implementation is committed.

`ChaCha20Precomputed.lean` targets the archived block-precomputation baseline
immediately before the raw-array round-loop optimization.

`ChaCha20RawRounds.lean` targets the archived raw-round-loop baseline
immediately before proof-bounded keystream table access.

The CSV data compares commit `1db9807` (`original`) with the working-tree
implementation (`current`). Both revisions successfully built their own
`Correctness.lean` and RFC tests against the unchanged `Spec.lean`. Checksums
agree for every measured input size.

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build Crypto.Stream.ChaCha20.Correctness Crypto.Stream.ChaCha20.Tests chacha20_bench
.lake/build/bin/chacha20_bench VERSION_LABEL
lake build Crypto.Stream.ChaCha20.Archive.OriginalCorrectness chacha20_bench_original
.lake/build/bin/chacha20_bench_original original
lake build Crypto.Stream.ChaCha20.Archive.PrecomputedCorrectness chacha20_bench_precomputed
.lake/build/bin/chacha20_bench_precomputed precomputed
lake build Crypto.Stream.ChaCha20.Archive.RawRoundsCorrectness chacha20_bench_raw_rounds
.lake/build/bin/chacha20_bench_raw_rounds raw-rounds
python3 Bench/plot_results.py Bench/chacha20-original.csv Bench/chacha20-precomputed.csv \
  Bench/01-original-vs-precomputed.svg
python3 Bench/plot_results.py Bench/chacha20-precomputed.csv Bench/chacha20-raw-rounds.csv \
  Bench/02-precomputed-vs-raw-rounds.svg
python3 Bench/plot_results.py Bench/chacha20-raw-rounds-baseline.csv Bench/chacha20-bounded-access.csv \
  Bench/03-raw-rounds-vs-bounded-access.svg
```

For publication-quality measurements, close CPU-intensive applications,
connect AC power, and repeat the complete experiment several times.
