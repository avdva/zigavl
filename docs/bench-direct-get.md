# Direct get experiment

[Benchmark guide](benchmarks.md)

## Change

All four backends use the same direct tree-descent loop in `get`. It follows
child locations and returns on equality, without constructing the parent/direction
result that `locate` needs for insertion. The ordered-storage binary-search fast
path is retained. There is no PointerBased exception, runtime backend dispatch,
or new configuration. Node layouts and memory usage are unchanged.

The independent compact-free-slot experiment is not included in this branch.

## Tradeoff

PointerBased does not show a clear performance win from the direct loop.
The unified implementation prioritizes one traversal implementation over a
backend-specific exception for small measured differences. In the final pinned
comparison, PointerBased at 250,000 elements is mostly similar (about -1% to +1%
elapsed-time change), except post-churn lookup at about 3% slower. At 10,000
elements, hit lookup improves about 3%, while misses, mixed, and post-churn
lookup are about 5-6% slower. This is an explicit tradeoff, not an unconditional
speedup claim.

Early unpinned runs showed much larger inconsistent changes. This CPU has hybrid
cores, so those results are excluded from the final conclusions; final runs
pin every process to the same logical CPU. A previous backend-selected candidate
was superseded by this shared traversal.

## Code-generation check

Standalone exported i64-to-i64 lookup wrappers were compiled using
`zig build-obj -Ofast` and their assembly instruction lines compared. Counts
include the complete wrapper body, including ordered lookup where supported;
they are static counts, not instructions executed per operation.

| Wrapper | Baseline instructions | Unified instructions |
|---|---:|---:|
| PointerBased | 58 | 36 |
| ArrayBased | 114 | 67 |
| StableArrayBased | 130 | 79 |
| SplitArrayBased | 106 | 65 |

Smaller generated code does not by itself establish faster execution, as the
PointerBased measurements illustrate.

## Final comparison method

- Baseline: main at `75d364b`; candidate: direct get for all four backends.
- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Both binaries run with `taskset -c 4` on the same high-frequency SMT core.
- TuneD PowerProfiles selected `performance`; the measured core's governor, EPP,
  and platform profile were allowed to settle and verified between rounds.
  Original balanced/powersave/balance_performance settings were restored afterward.
- Seven alternating before/after rounds at 10,000 and 250,000 elements.
- Excluded 1,000-element lookup warmups validated all lookup scenarios per binary.
- Identical deterministic insertion/query seeds; each process rebuilds its trees.
  No compilation or tests ran alongside the timing comparisons.
- Filters: `lookup/i64/value8`, `lookup/i64/value256/hits`,
  `lookup/string32/value8/hits`.
- Ordered-storage lookup retains the same search algorithm and serves as a
  control; whole-program timings can still vary with code layout and system effects.

## Results

Median ns/op from seven samples. Positive reduction means less elapsed time.

### 10,000 elements

| Scenario | Before ns/op | Unified ns/op | Reduction |
|---|---:|---:|---:|
| `pointer/lookup/i64/value8/hits` | 90.6 | 87.5 | +3.4% |
| `pointer/lookup/i64/value8/misses` | 104.5 | 109.3 | -4.6% |
| `pointer/lookup/i64/value8/mixed` | 97.3 | 102.7 | -5.5% |
| `pointer/lookup/i64/value8/churn` | 91.5 | 97.1 | -6.1% |
| `array/lookup/i64/value8/hits` | 135.4 | 81.5 | +39.8% |
| `array/lookup/i64/value8/misses` | 141.9 | 91.9 | +35.2% |
| `array/lookup/i64/value8/mixed` | 135.3 | 88.0 | +35.0% |
| `array/lookup/i64/value8/churn` | 128.6 | 82.6 | +35.8% |
| `array/lookup/i64/value8/ordered` | 62.2 | 57.7 | +7.3% |
| `stable-array/lookup/i64/value8/hits` | 140.2 | 95.9 | +31.6% |
| `stable-array/lookup/i64/value8/misses` | 151.1 | 103.8 | +31.3% |
| `stable-array/lookup/i64/value8/mixed` | 146.4 | 99.3 | +32.2% |
| `stable-array/lookup/i64/value8/churn` | 140.4 | 90.7 | +35.4% |
| `stable-array/lookup/i64/value8/ordered` | 72.8 | 69.8 | +4.1% |
| `split-array/lookup/i64/value8/hits` | 123.8 | 75.0 | +39.4% |
| `split-array/lookup/i64/value8/misses` | 131.7 | 85.5 | +35.1% |
| `split-array/lookup/i64/value8/mixed` | 132.1 | 83.4 | +36.9% |
| `split-array/lookup/i64/value8/churn` | 125.5 | 77.2 | +38.4% |
| `split-array/lookup/i64/value8/ordered` | 63.9 | 65.0 | -1.6% |
| `pointer/lookup/i64/value256/hits` | 119.8 | 120.9 | -0.9% |
| `array/lookup/i64/value256/hits` | 147.2 | 98.1 | +33.4% |
| `stable-array/lookup/i64/value256/hits` | 156.7 | 103.6 | +33.9% |
| `split-array/lookup/i64/value256/hits` | 128.9 | 75.5 | +41.4% |
| `pointer/lookup/string32/value8/hits` | 307.7 | 314.1 | -2.1% |
| `array/lookup/string32/value8/hits` | 339.7 | 308.0 | +9.3% |
| `stable-array/lookup/string32/value8/hits` | 357.6 | 322.1 | +9.9% |
| `split-array/lookup/string32/value8/hits` | 360.8 | 323.8 | +10.2% |

### 250,000 elements

| Scenario | Before ns/op | Unified ns/op | Reduction |
|---|---:|---:|---:|
| `pointer/lookup/i64/value8/hits` | 265.4 | 266.8 | -0.5% |
| `pointer/lookup/i64/value8/misses` | 345.3 | 342.5 | +0.8% |
| `pointer/lookup/i64/value8/mixed` | 314.4 | 314.3 | +0.1% |
| `pointer/lookup/i64/value8/churn` | 284.7 | 293.5 | -3.1% |
| `array/lookup/i64/value8/hits` | 236.4 | 169.1 | +28.5% |
| `array/lookup/i64/value8/misses` | 257.4 | 189.5 | +26.4% |
| `array/lookup/i64/value8/mixed` | 247.5 | 179.9 | +27.3% |
| `array/lookup/i64/value8/churn` | 244.6 | 183.0 | +25.2% |
| `array/lookup/i64/value8/ordered` | 122.0 | 119.0 | +2.5% |
| `stable-array/lookup/i64/value8/hits` | 251.2 | 181.6 | +27.7% |
| `stable-array/lookup/i64/value8/misses` | 274.7 | 206.6 | +24.8% |
| `stable-array/lookup/i64/value8/mixed` | 266.1 | 197.8 | +25.7% |
| `stable-array/lookup/i64/value8/churn` | 262.1 | 195.2 | +25.5% |
| `stable-array/lookup/i64/value8/ordered` | 138.6 | 131.7 | +4.9% |
| `split-array/lookup/i64/value8/hits` | 232.2 | 150.6 | +35.1% |
| `split-array/lookup/i64/value8/misses` | 244.6 | 170.4 | +30.3% |
| `split-array/lookup/i64/value8/mixed` | 242.3 | 161.7 | +33.3% |
| `split-array/lookup/i64/value8/churn` | 247.2 | 169.8 | +31.3% |
| `split-array/lookup/i64/value8/ordered` | 105.8 | 102.7 | +2.9% |
| `pointer/lookup/i64/value256/hits` | 493.5 | 493.2 | +0.1% |
| `array/lookup/i64/value256/hits` | 347.7 | 264.6 | +23.9% |
| `stable-array/lookup/i64/value256/hits` | 357.7 | 282.6 | +21.0% |
| `split-array/lookup/i64/value256/hits` | 324.5 | 160.1 | +50.7% |
| `pointer/lookup/string32/value8/hits` | 592.0 | 587.4 | +0.8% |
| `array/lookup/string32/value8/hits` | 593.1 | 509.0 | +14.2% |
| `stable-array/lookup/string32/value8/hits` | 613.4 | 547.8 | +10.7% |
| `split-array/lookup/string32/value8/hits` | 669.7 | 611.4 | +8.7% |

## Interpretation and limitations

The address-backed tree-descent paths show substantial elapsed-time reductions
in these runs, including large-value and fixed-width string-key scenarios.
PointerBased is mostly similar on the larger tree and has some small-tree
regressions, as described above. The report records the shared implementation;
it no longer mixes timings from the backend-selected variant with unified code.

Controls vary too. Do not attribute small differences in ordered lookup to the
new descent loop or claim that every scenario improves. Short small-tree timings
are especially sensitive to system and code-layout effects, even with fixed CPU
affinity. Measurements on this compiler and machine are not cross-platform
guarantees; other targets and workloads should be checked before broader claims.

## Validation and reproduction

- 66/66 tests pass in Debug and ReleaseSafe for the unified implementation.
- The added lookup test covers empty trees, hits/misses, extreme i64 keys,
  ascending/reverse comparators, pointer writes, ordered storage, and lookups
  after deletion/insertion across all four backends.
- All 76 lookup scenarios pass as the excluded warmup at size 1,000.
- Timed workloads validate hit counts, checksums, and tree length outside timing.
- Formatting and diff checks pass.

Build each revision with `zig build install-bench -Doptimize=ReleaseFast` and
save separate binaries. Set and verify the performance power profile, pin both
binaries to the same suitable CPU, then alternate commands such as:

```sh
taskset -c 4 ./before lookup/i64/value8 --size=250000
taskset -c 4 ./after lookup/i64/value8 --size=250000
```

Use the same filters and sizes above for seven rounds, reversing binary order
between rounds. Choose an appropriate CPU for the machine rather than copying
CPU 4 blindly, and restore the original power profile when finished.
