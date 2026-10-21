# Benchmark guide

[README](../README.md) · [Storage backends](caches.md)

Use the benchmark suite to compare storage backends for the operations and
key/value types your application uses. A single result does not identify the
best backend for every workload.

## Running the suite

Run the basic benchmark suite with:

```sh
zig build bench -Doptimize=ReleaseFast
```

The suite includes positional lookup benchmarks for the regular `O(logn)`
count-based path, the `O(1)` ordered-storage path, and the ordered-storage path
including the one-time `orderStorageByKey()` cost.

Additional lookup workloads cover randomly inserted trees, interleaved missing
keys, a 50/50 hit/miss mix, lookups after replacing 25% of nodes, and ordered
storage. They compare all four storage backends with 8-, 64-, and 256-byte
values, plus fixed-width 32-byte string keys with a shared prefix (8-byte values).
The timed region includes lookup and reading one value byte; insertion, key
formatting, mutation, ordering, and validation are outside it. Query order is
shuffled independently from insertion order with deterministic seeds.

Use `-Dbench-filter` for a substring filter, `-Dbench-size` (4 to 10,000,000;
default 250,000), and `-Dbench-repeat` (default 1). Size applies to both existing and new benchmarks.
Each repetition rebuilds the trees and prints its own result; no aggregation
or warmup samples are hidden. Compare repeated runs rather than one sample.

```sh
zig build bench -Doptimize=ReleaseFast -Dbench-filter=lookup -Dbench-size=10000 -Dbench-repeat=5
zig build bench -Doptimize=ReleaseFast -Dbench-filter=lookup -Dbench-size=250000 -Dbench-repeat=5
zig build bench -Doptimize=ReleaseFast -Dbench-filter=lookup -Dbench-size=1000000 -Dbench-repeat=5
zig build bench -Doptimize=ReleaseFast -Dbench-filter=split-array/lookup/i64/value256
zig build bench -Doptimize=ReleaseFast -Dbench-filter=lookup/string32
```

The executable installed by `zig build install-bench` also accepts a positional
substring filter, `--size`, and `--repeat` directly.

`insert-matrix` compares ascending, descending, random, and existing-key update
workloads for all backends, with and without subtree counts, using `i64` and
fixed-width 32-byte string keys. Key generation, string formatting, and tree
initialization happen before timing. Existing-key updates prefill the tree outside timing; other
workloads include allocation and insertion into an initially empty tree.
Checksums, insertion counts, final length, and every stored value are validated
outside timing. Each sample uses a fresh tree and the suite's fixed allocator.

```sh
zig build bench -Doptimize=ReleaseFast -Dbench-filter=insert-matrix -Dbench-size=250000 -Dbench-repeat=7
zig build bench -Doptimize=ReleaseFast -Dbench-filter=insert-matrix/string32/uncounted/random
```

The `hits` case reads every inserted key once; `misses` queries the adjacent odd
keys; `mixed` alternates hits and misses in shuffled order. The `churn` case
removes the first quarter of the shuffled insertion sequence, inserts replacement
keys above the original range, and then looks up all live keys. The `ordered`
case measures lookup after `orderStorageByKey()` and excludes pointer storage.
Hit counts, checksums, and tree length are checked outside timing even in
ReleaseFast. Existing `get/random` remains the sequentially built baseline.

`delete-extreme` drains identically constructed trees from the first or last
key using `pop`, `by_key` (`delete(key)`), or `by_index` (`deleteAt`). The matrix
covers all backends with and without subtree counts, and both ordinary and
ordered storage where supported. The input is a fixed shuffle of dense i64 keys.
Tree construction, optional storage ordering, and result-buffer allocation are
outside timing. Each method writes every removed `KV` to the same kind of
buffer; all keys, values, and the final empty state are checked afterward.
`by_key` receives the known next key and does not call `getMin`/`getMax` in its
timed loop. Method order rotates across `--repeat` repetitions; backend and
layout order remain fixed.

```sh
zig build bench -Doptimize=ReleaseFast -Dbench-filter=delete-extreme -Dbench-size=250000 -Dbench-repeat=7
zig build bench -Doptimize=ReleaseFast -Dbench-filter=delete-extreme/uncounted/tree/first
```

See the [popFirst/popLast comparison](bench-pop-extremes.md) for measurements
against existing deletion methods and the limits of this workload.

See [the array node layout experiment](bench-node-layout.md) for measured
slot sizes, comparison methodology, and preliminary timing results.

## Recommendations and limitations

- Use ReleaseFast for throughput comparisons and the same Zig version, target,
  allocator, and build settings for both revisions.
- Start with a small size to validate a scenario, then compare sizes below and
  above the CPU cache capacity. Large values and million-element trees can use
  substantial memory; avoid swapping during measurements.
- Run several repetitions and compare medians and spread. The executable prints
  individual samples; it does not compute statistics or discard warmup runs.
  Very small trees are useful for correctness checks but timings may be dominated
  by timer and loop overhead.
- Keep heavy background work, compilation, and tests out of timing runs. On a
  laptop, use consistent power settings and alternate before/after process order
  to reduce temperature and frequency bias.
- Keep insertion/query seeds and inputs identical across revisions. Deterministic
  seeds make comparisons reproducible but do not cover every tree shape.
- Keep an unchanged backend as a control. Changes of a few percent may reflect
  measurement noise; inspect the controls before attributing a speedup to code.
- Large-value lookup scenarios read only one byte of the returned value. They
  measure the effect of storage layout on search, not the cost of processing or
  copying an entire value. String scenarios use inline fixed-width keys, not
  separately allocated strings or arbitrary-length string comparisons.
- `ordered` lookup excludes the one-time ordering cost. Include that cost when
  deciding whether ordering pays off for a real workload. The positional
  `at/ordered-including-order` scenario includes it for that specific operation.
- The `churn` lookup measures reads after a fixed replacement phase, not a timed
  mixture of reads and writes. Use the existing delete-insert scenarios to
  measure mutation cost as well.

The suite currently uses a fixed allocator and fixed key/payload families.
For application decisions, add representative distributions, comparator costs,
mutation rates, and lifetimes rather than extrapolating from integer keys alone.

See the [direct get experiment](bench-direct-get.md) for a shared-traversal
lookup comparison, generated-code inspection, and measurements with fixed CPU
affinity. On hybrid CPUs, pin before/after processes to the same logical CPU
(e.g. with `taskset` on Linux) and record the chosen core alongside the power
profile. A performance power profile alone does not fix CPU affinity.

See the [edge-insertion experiment](bench-extreme-insertion.md) for an adaptive
minimum/maximum insertion shortcut and its effect on monotonic and random keys.
