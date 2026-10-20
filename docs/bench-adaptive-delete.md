# Adaptive edge lookup in delete(key)

[Benchmark guide](benchmarks.md) · [Direct edge removal](bench-pop-extremes.md)

## Change

After removal of a minimum or maximum, `delete(key)` first compares its next
key against the current edge in that direction. Equality supplies the location
directly to the existing deletion path. A miss disables the hint and falls back
to ordinary root search. Deleting an interior node also disables the hint.

Shared deletion records the direction using its existing min/max checks; no
additional search is needed to train the hint. The hint stores a direction,
not a node address, and resolves current edges after insertions, rotations,
compaction, ordering, or key updates. Clearing resets it. Empty trees remain
safe even when their last deletion left a direction hint enabled.

The first removal of a monotonic run uses ordinary search. Subsequent removals
use one key comparison to resolve the edge. Rebalancing, extrema maintenance,
and subtree counts still have `O(log n)` worst-case cost. Alternating ends and
random keys may fall back to root search; they are not promised an improvement.
`popFirst()`/`popLast()` still perform zero key comparisons, but their shared
deletion path also updates the hint.

For the measured x86_64 uncounted i64-to-i64 trees, object sizes remain unchanged:
PointerBased 104 bytes, ArrayBased 120, StableArrayBased 128, SplitArrayBased 216.
The direction fits existing padding; this does not guarantee identical layout
costs for other types or targets. Node layouts are unchanged.

## Method

- Baseline: `6c11ee1`, including popFirst/popLast, with the same added benchmark
  matrix copied into both builds. Candidate adds only adaptive deletion and
  regression tests to that library code.
- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Seven alternating baseline/candidate process pairs at 10,000 and 250,000
  elements. Excluded 1,000-element runs validate the scenarios first.
- Processes are pinned with `taskset -c 4`. Performance governor, energy
  preference, and platform profile are verified after settling. Original power
  settings are restored after timing; no compilation or tests overlap it.
- `delete-adaptive` covers all four backends, counted/uncounted i64 keys, and
  uncounted fixed-width 32-byte string keys. Each variant runs the same 48 cases.
- Every scenario builds a fresh tree from the same shuffled even keys. Timed
  queries remove first keys, last keys, or shuffled existing keys, or query
  shuffled interleaved missing odd keys. Missing-key scenarios first delete key
  zero outside timing to exercise a prediction miss and its fallback.
- Tree construction, query formatting, and result-buffer allocation are outside
  timing. Returned values are stored in the same kind of optional-value buffer
  and checked afterward. Missing-key scenarios also validate every surviving
  value. Values differ from keys (`id * 10 + 7`) to catch incorrect results.
- This matrix uses ordinary storage. Ordered-storage correctness is covered by
  regression tests; these timings do not establish ordered-workload speedups.

## Validation

All 76 tests pass in Debug and ReleaseSafe, alongside the existing expected
unsupported-reservation compile error. The keyed-deletion matrix covers every
backend/count setting with normal/reversed comparators, first/last/alternating
ends, exactly one comparison for continued edge runs, empty trees, missing
queries, insertion after prediction, compaction, ordering, bulk replacement,
updateKey, extreme i64 keys, ranks, and AVL invariants. Direct-pop tests still
verify zero comparator calls.

## Keyed-deletion results

Median ns/op at 250,000 elements without subtree counts. Negative percentages
mean less elapsed time. The [full CSV](bench-adaptive-delete.csv) contains all
96 size/scenario combinations, both count settings for i64, and seven-sample
minimum/maximum values.

### i64 keys

| Backend | First-key run | Last-key run | Random deletion | Missing keys |
|---|---:|---:|---:|---:|
| pointer | 74.0 → 60.3 (-18.6%) | 70.9 → 57.2 (-19.4%) | 286.0 → 285.9 (-0.0%) | 359.3 → 345.4 (-3.9%) |
| array | 163.5 → 77.4 (-52.7%) | 157.6 → 75.6 (-52.0%) | 298.7 → 300.7 (+0.7%) | 249.6 → 254.5 (+1.9%) |
| stable-array | 191.2 → 95.4 (-50.1%) | 184.5 → 90.0 (-51.2%) | 319.4 → 324.8 (+1.7%) | 275.6 → 272.8 (-1.0%) |
| split-array | 175.4 → 77.3 (-55.9%) | 171.0 → 76.5 (-55.3%) | 292.5 → 299.7 (+2.5%) | 235.2 → 243.5 (+3.5%) |

### string32 keys

| Backend | First-key run | Last-key run | Random deletion | Missing keys |
|---|---:|---:|---:|---:|
| pointer | 345.6 → 83.5 (-75.8%) | 339.8 → 81.5 (-76.0%) | 615.0 → 624.1 (+1.5%) | 695.0 → 698.5 (+0.5%) |
| array | 422.1 → 94.9 (-77.5%) | 418.0 → 94.4 (-77.4%) | 605.4 → 611.9 (+1.1%) | 622.8 → 631.5 (+1.4%) |
| stable-array | 445.7 → 103.2 (-76.8%) | 442.1 → 103.6 (-76.6%) | 628.2 → 635.8 (+1.2%) | 650.7 → 651.0 (+0.0%) |
| split-array | 463.3 → 108.0 (-76.7%) | 457.6 → 107.4 (-76.5%) | 669.8 → 671.8 (+0.3%) | 691.6 → 697.8 (+0.9%) |

### Scope and tradeoffs

Edge runs at 10,000 elements span -78.5% to -11.3% elapsed-time change across the measured backends, key types, and count settings; median scenario change -47.5%.

Random and missing-key queries at 10,000 elements span -3.9% to +3.6% elapsed-time change across the measured backends, key types, and count settings; median scenario change +0.1%.

Edge runs at 250,000 elements span -77.5% to -18.6% elapsed-time change across the measured backends, key types, and count settings; median scenario change -51.6%.

Random and missing-key queries at 250,000 elements span -3.9% to +3.5% elapsed-time change across the measured backends, key types, and count settings; median scenario change +0.8%.

The adaptive check has a cost: at 250,000 elements, uncounted SplitArrayBased
i64 misses change from 235.2 to 243.5 ns/op (+3.5%), and random deletions from
292.5 to 299.7 ns/op (+2.5%). At 10,000 elements, counted PointerBased random
deletion changes from 148.9 to 154.3 ns/op (+3.6%). These are workload-dependent
tradeoffs; the medians across scenarios do not weight an application mix or
establish statistical significance.

## Direct-pop controls

A separate seven-pair comparison runs `/pop` from the existing `delete-extreme`
matrix, covering all backends/count settings and ordinary/ordered storage.
The same alternating process order, CPU affinity, power verification, and sizes
apply. Power settings were restored after this comparison as well. The
[control CSV](bench-adaptive-delete-pop-controls.csv) contains all 56 summaries.

At 10,000 elements, pop elapsed-time changes range from -9.7% to +7.6%, with median scenario change +1.0%.

At 250,000 elements, pop elapsed-time changes range from -1.5% to +1.5%, with median scenario change +0.1%.

The largest measured increase is array counted tree last at 10,000 elements: 132.7 to 142.8 ns/op (+7.6%). This shared-path bookkeeping is not free in every scenario, even though direct pops still make no key comparisons.
