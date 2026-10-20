# Insertion along an edge

[Benchmark guide](benchmarks.md)

## Change

After an insertion extends the minimum or maximum, the next insertion first
compares against that same cached edge. If it also extends the edge, its parent
is already known; insertion skips the search from the root and uses the existing
linking and AVL rebalancing code. An equal key returns the existing entry.

A failed edge probe disables the hint and falls back to the regular search.
Inserting an interior key also disables the hint. A later insertion that extends
an edge enables it again. The first two insertions of an initially monotonic
sequence use ordinary search; subsequent insertions need one key comparison to
find their parent. A change of direction or alternating minima and maxima can
fall back to ordinary search. Total insertion complexity remains `O(log n)`;
subtree counts and rebalancing still need maintenance.

The hint stores a direction, not a location. It always uses the current `min`
or `max`, so deletion, storage compaction, and storage ordering do not leave a
cached node address behind. Clearing resets the hint. `insert`, `getOrInsert`,
and `getOrEmplace` share this path across all four backends. Other search APIs
and `updateKey` retain their existing traversal.

No node layout changes are involved. On the measured x86_64 target, the
uncounted i64-to-i64 tree object sizes are unchanged: PointerBased 104 bytes,
ArrayBased 120, StableArrayBased 128, and SplitArrayBased 216. The direction fits
in existing padding; other types and targets may have different layout costs.

## Method

- Baseline: `main` at `dce185e`, with the same new insertion benchmark matrix.
- Candidate: the adaptive edge hint described above.
- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Each process is pinned with `taskset -c 4`. PowerProfiles selects `performance`;
  CPU governor, energy preference, and platform profile are checked after they
  settle. The original balanced/powersave/balance_performance settings are
  restored after measurement.
- Seven alternating before/after rounds at 10,000 and 250,000 elements.
- Separate 1,000-element warmups validate all scenarios and are excluded.
- `insert-matrix` covers all backends, both subtree-count settings, i64 and
  fixed-width string keys, and ascending/descending/random/existing-key workloads.
- Every sample uses a fresh tree, identical keys and allocator, and validates
  every final value, length, insertion count, and checksum outside timing.
  New-key timings include allocation during insertion; tree initialization and
  existing-key prefill are excluded.
- No compilation or tests run alongside the timed comparisons.

These measurements describe one CPU, allocator, and set of workloads, not a
universal speedup. Inspect random insertion and existing-key updates as well as
monotonic sequences before choosing this optimization.

## Results

The tables show median ns/op, baseline to candidate, for 250,000 elements
without subtree counts. Percentages are elapsed-time changes: negative is faster.
The [complete CSV](bench-extreme-insertion.csv) includes all 128 size/scenario
combinations, both count settings, and each seven-sample minimum/maximum.

### i64 keys

| Backend | Ascending | Descending | Random | Existing-key update |
|---|---:|---:|---:|---:|
| pointer | 135.0 → 55.2 (-59.1%) | 96.5 → 30.2 (-68.7%) | 235.8 → 234.7 (-0.4%) | 290.2 → 279.7 (-3.6%) |
| array | 130.3 → 37.4 (-71.3%) | 137.4 → 43.5 (-68.4%) | 266.1 → 278.6 (+4.7%) | 211.8 → 218.2 (+3.0%) |
| stable-array | 159.0 → 50.6 (-68.2%) | 169.9 → 58.9 (-65.3%) | 297.7 → 299.1 (+0.5%) | 233.8 → 233.9 (+0.0%) |
| split-array | 138.4 → 33.0 (-76.2%) | 147.4 → 40.7 (-72.4%) | 265.3 → 267.7 (+0.9%) | 206.1 → 206.1 (+0.0%) |

### string32 keys

| Backend | Ascending | Descending | Random | Existing-key update |
|---|---:|---:|---:|---:|
| pointer | 391.0 → 102.6 (-73.8%) | 395.0 → 98.4 (-75.1%) | 624.9 → 627.0 (+0.3%) | 593.4 → 591.7 (-0.3%) |
| array | 416.7 → 55.5 (-86.7%) | 431.3 → 60.3 (-86.0%) | 614.1 → 618.2 (+0.7%) | 559.0 → 564.5 (+1.0%) |
| stable-array | 447.6 → 64.3 (-85.6%) | 459.4 → 68.5 (-85.1%) | 640.7 → 640.0 (-0.1%) | 579.9 → 573.1 (-1.2%) |
| split-array | 459.7 → 53.6 (-88.3%) | 471.3 → 60.8 (-87.1%) | 681.7 → 683.2 (+0.2%) | 621.1 → 620.4 (-0.1%) |

### Scope and tradeoffs

Across all key types, backends, and count settings, monotonic sequences reduce
elapsed time by 19–83% at 10,000 elements and 29–88% at 250,000 elements.

Random insertion and existing-key updates range from -4.7% to +8.0% elapsed-time
change at 10,000 elements, with a median scenario change of +0.9%. At 250,000
these workloads range from -5.8% to +4.7%, with a median scenario change close
to zero. These medians describe the scenario set; they do not weight scenarios
by an application's workload or establish statistical significance.

There are remaining regressions worth considering. For uncounted ArrayBased
i64 trees, random insertion changes from 158.3 to 170.6 ns/op (+7.7%) at 10,000
elements and 266.1 to 278.6 ns/op (+4.7%) at 250,000. Existing-key updates at
10,000 change from 114.2 to 123.3 ns/op (+8.0%). The optimization suits workloads
with monotonic runs; it is not an unconditional improvement for random keys.
The adaptive hint limits extra comparisons after an interior insertion, but
still adds state checks and updates and can change generated code layout.

## Validation

All 74 tests pass in Debug and ReleaseSafe, alongside the expected
unsupported-reservation compile error. The new regression test covers every
backend and count setting with normal and reversed comparators, monotonic and
alternating-edge keys, all three insertion APIs, duplicate updates and
constructor-call counts, deleted extrema, ordered storage, clearing, extreme
i64 keys, sorted iteration, ranks, and AVL invariants. The benchmark matrix
also validates integer and string scenarios outside timing in ReleaseFast.
