# Removing the first and last elements

[Benchmark guide](benchmarks.md) · [API semantics](caches.md#removing-the-first-or-last-element)

## Change

`deleteFirst()` and `deleteLast()` copy the key/value pair at the cached `min` or
`max` location and pass that location directly to `deleteLocation()`. An empty
tree returns `null`. This skips root search and key comparisons without adding
checks, hints, or fields to ordinary deletion. Rebalancing and subtree-count
maintenance are shared with the existing deletion APIs; worst-case complexity
remains `O(log n)`.

`deleteAt(0)` and `deleteAt(len() - 1)` already find these edges directly. The
benchmark compares against them as well as `delete(key)`: these methods provide
an explicit optional-result API, and should not be assumed faster than indexed
edge deletion. First/last follow comparator order, including reversed comparators.

## Method

- Base: `main` at `c9ffab8`; all methods are compared within the same candidate
  executable, with no change to ordinary `delete(key)` or `deleteAt()`.
- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Every process runs on logical CPU 4 with `taskset -c 4`. The performance power
  profile, CPU governor, energy preference, and platform profile settle before
  timing. Original balanced/powersave/balance_performance settings are restored.
- Seven repetitions at 10,000 and 250,000 elements; an excluded 1,000-element
  run validates all scenarios first. Method order rotates between repetitions;
  backend and storage-layout order remain fixed.
- All four backends, both subtree-count settings, and first/last deletion.
  Address-based backends also run after `orderStorageByKey()`.
- Each scenario starts with a fresh tree built from the same deterministic
  shuffle of dense i64 keys. Values are `key * 10 + 7`.
- Tree construction, storage ordering, and result-buffer allocation are outside
  timing. Every method stores each removed pair in the result buffer. Full key
  and value sequences and the final empty state are checked after timing.
- `delete(key)` receives the known next key; it does not perform a separate
  `getMin()` or `getMax()` call in the timed loop. `deleteAt()` uses index zero
  or the current `len() - 1`.
- Deleting the last element preserves ordered storage while the tree is nonempty.
  Deleting the first invalidates ordering after the first removal, so that
  scenario measures draining a tree initially stored in key order.
- No compilation or tests run alongside timing. Timings include the common
  result-buffer writes and allocator frees where the backend performs them.

This comparison uses i64 keys/values and one allocator. Comparator costs, node
sizes, hardware, and how often an application removes an edge affect the gain.
Small differences against indexed deletion may reflect code generation and
measurement variation rather than a consistently faster algorithm.

## Validation

All 75 tests pass in Debug and ReleaseSafe, alongside the existing expected
unsupported-reservation compile error. The regression matrix covers every
backend, count setting, and normal/reversed comparator. It verifies zero
comparator calls during edge deletions, every returned key/value pair, repeated empty
calls, refill and slot reuse, deleted slots, ordered-storage preservation and
invalidation, alternating ends, extreme i64 keys, ranks, and AVL invariants.
The public consumer test and updated README example also exercise the methods.

## Results

Timings were collected before the unreleased methods were renamed from
`popFirst`/`popLast` to `deleteFirst`/`deleteLast`. Only API references and the
benchmark label (`pop` to `by_edge`) were updated; numeric results are unchanged.

Median ns/op at 250,000 elements without subtree counts. Percentages compare
by_edge elapsed time with the named alternative: negative is faster. The
[full CSV](bench-delete-extremes.csv) includes both sizes, count settings, storage
layouts, and minimum/maximum values across seven samples (168 summaries).

### Ordinary storage

| Backend | End | delete(key) | deleteAt | by_edge | vs key | vs index |
|---|---|---:|---:|---:|---:|---:|
| pointer | first | 71.4 | 53.8 | 53.7 | -24.8% | -0.2% |
| pointer | last | 69.2 | 53.5 | 51.7 | -25.2% | -3.3% |
| array | first | 157.7 | 73.9 | 70.2 | -55.5% | -5.0% |
| array | last | 153.7 | 72.8 | 70.3 | -54.3% | -3.4% |
| stable-array | first | 187.3 | 90.2 | 88.5 | -52.7% | -1.9% |
| stable-array | last | 179.7 | 86.3 | 84.4 | -53.1% | -2.2% |
| split-array | first | 168.4 | 75.9 | 70.3 | -58.3% | -7.4% |
| split-array | last | 165.2 | 75.5 | 70.6 | -57.3% | -6.5% |

### Initially ordered storage

| Backend | End | delete(key) | deleteAt | by_edge | vs key | vs index |
|---|---|---:|---:|---:|---:|---:|
| array | first | 142.4 | 59.0 | 57.9 | -59.3% | -1.8% |
| array | last | 139.7 | 57.8 | 58.0 | -58.5% | +0.3% |
| stable-array | first | 171.4 | 78.1 | 75.2 | -56.1% | -3.7% |
| stable-array | last | 165.1 | 72.5 | 73.1 | -55.7% | +0.8% |
| split-array | first | 133.6 | 59.6 | 53.4 | -60.0% | -10.3% |
| split-array | last | 131.5 | 58.3 | 54.4 | -58.6% | -6.7% |

### Scope and tradeoffs

Across all backends, count settings, layouts, and ends at 10,000 elements, by_edge versus by_key ranges from -54.8% to -10.8% elapsed-time change; the median scenario change is -33.5%.

Across all backends, count settings, layouts, and ends at 10,000 elements, by_edge versus by_index ranges from -20.6% to +15.0% elapsed-time change; the median scenario change is -1.5%.

Across all backends, count settings, layouts, and ends at 250,000 elements, by_edge versus by_key ranges from -60.0% to -23.1% elapsed-time change; the median scenario change is -35.7%.

Across all backends, count settings, layouts, and ends at 250,000 elements, by_edge versus by_index ranges from -10.3% to +0.8% elapsed-time change; the median scenario change is -1.6%.

The small-tree comparison against indexed deletion has wider spread. Counted
PointerBased `deleteLast` at 10,000 elements measures 38.4 versus 33.4 ns/op
(+15.0%), with seven-sample ranges of 31.7–40.5 and 31.6–40.2 ns/op respectively.
Counted SplitArrayBased `deleteLast` measures 136.4 versus 120.4 ns/op (+13.3%).
These results do not support a universal speedup over `deleteAt()`. The
consistent distinction is removal of key search relative to `delete(key)` and
an explicit empty-safe API. Medians across scenarios are descriptive, not
weighted application results or a statistical significance test.
