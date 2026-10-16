# Direct get experiment

[Benchmark guide](benchmarks.md)

## Change

For ArrayBased, StableArrayBased, and SplitArrayBased, `get` descends directly
through child locations and returns on equality. It does not construct the
parent/direction result that `locate` needs for insertion. The ordered-storage
binary-search path is retained. PointerBased retains its original `locate` path;
this choice uses the existing compile-time backend option, with no runtime
dispatch or new configuration. Node layouts and memory usage are unchanged.

The independent compact-free-slot experiment is not included in this branch.

## Why retain locate for PointerBased?

An initial prototype used direct descent for all backends. Unpinned runs showed
large inconsistent changes even in the pointer controls. This CPU has hybrid
cores, so final comparisons pin every process to the same logical CPU.
The unpinned timing results are excluded from the final conclusions.

An isolated pinned comparison of baseline, all-direct prototype, and final
backend-selected candidate found no clear PointerBased win from direct descent.
At 250,000 elements, the all-direct prototype's pointer scenarios were roughly
0-2% slower; at 10,000 they ranged from 2% faster to 3% slower. Retaining the
existing path is the conservative choice. The large initial unpinned regression
did not reproduce with fixed affinity; its exact cause was not established.

## Code-generation check

Standalone exported i64-to-i64 lookup wrappers were compiled using
`zig build-obj -Ofast` and their assembly instruction lines compared. Counts
include the complete wrapper body, including ordered lookup where supported;
they are static counts, not instructions executed per operation.

| Wrapper | Baseline instructions | Final instructions |
|---|---:|---:|
| PointerBased | 58 | 58 |
| ArrayBased | 114 | 67 |
| StableArrayBased | 130 | 79 |
| SplitArrayBased | 106 | 65 |

The PointerBased probe's instruction sequence is identical to baseline.
The all-direct prototype had 36 instructions in that probe, illustrating that
smaller code alone does not establish better runtime performance.

## Final comparison method

- Baseline: main at `75d364b`; candidate: direct get for address-based backends.
- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Both binaries run with `taskset -c 4` on the same high-frequency SMT core.
- TuneD PowerProfiles selected `performance`; governor, EPP, and platform profile
  were allowed to settle and verified. The measured core's settings were also
  checked during the run. Original balanced/powersave/balance_performance settings
  were restored afterward.
- Seven alternating before/after rounds at 10,000 and 250,000 elements.
- Excluded 1,000-element lookup warmups validated all lookup scenarios per binary.
- Identical deterministic insertion/query seeds; each process rebuilds its trees.
  No compilation or tests ran alongside the timing comparisons.
- Filters: `lookup/i64/value8`, `lookup/i64/value256/hits`,
  `lookup/string32/value8/hits`.
- Pointer and ordered-storage algorithms are unchanged and serve as controls.
  Their whole-program timings can still vary with code layout and system effects.

## Results

Median ns/op from seven samples. Positive reduction means less elapsed time.

### 10,000 elements

| Scenario | Before ns/op | After ns/op | Reduction |
|---|---:|---:|---:|
| `pointer/lookup/i64/value8/hits` | 93.3 | 88.2 | +5.5% |
| `pointer/lookup/i64/value8/misses` | 106.2 | 105.4 | +0.8% |
| `pointer/lookup/i64/value8/mixed` | 97.4 | 98.3 | -0.9% |
| `pointer/lookup/i64/value8/churn` | 93.2 | 92.0 | +1.3% |
| `array/lookup/i64/value8/hits` | 130.1 | 81.6 | +37.3% |
| `array/lookup/i64/value8/misses` | 144.9 | 91.1 | +37.1% |
| `array/lookup/i64/value8/mixed` | 138.2 | 86.3 | +37.6% |
| `array/lookup/i64/value8/churn` | 127.7 | 80.5 | +37.0% |
| `array/lookup/i64/value8/ordered` | 63.1 | 69.6 | -10.3% |
| `stable-array/lookup/i64/value8/hits` | 148.1 | 94.2 | +36.4% |
| `stable-array/lookup/i64/value8/misses` | 154.0 | 103.8 | +32.6% |
| `stable-array/lookup/i64/value8/mixed` | 153.7 | 95.4 | +37.9% |
| `stable-array/lookup/i64/value8/churn` | 139.9 | 93.0 | +33.5% |
| `stable-array/lookup/i64/value8/ordered` | 73.0 | 67.8 | +7.2% |
| `split-array/lookup/i64/value8/hits` | 123.1 | 74.0 | +39.9% |
| `split-array/lookup/i64/value8/misses` | 132.1 | 84.4 | +36.1% |
| `split-array/lookup/i64/value8/mixed` | 131.9 | 81.2 | +38.4% |
| `split-array/lookup/i64/value8/churn` | 128.9 | 78.9 | +38.8% |
| `split-array/lookup/i64/value8/ordered` | 65.2 | 59.5 | +8.8% |
| `pointer/lookup/i64/value256/hits` | 120.1 | 117.7 | +2.0% |
| `array/lookup/i64/value256/hits` | 146.9 | 101.4 | +30.9% |
| `stable-array/lookup/i64/value256/hits` | 154.2 | 103.0 | +33.2% |
| `split-array/lookup/i64/value256/hits` | 131.1 | 72.0 | +45.1% |
| `pointer/lookup/string32/value8/hits` | 303.1 | 307.1 | -1.3% |
| `array/lookup/string32/value8/hits` | 344.4 | 302.9 | +12.1% |
| `stable-array/lookup/string32/value8/hits` | 357.6 | 325.6 | +8.9% |
| `split-array/lookup/string32/value8/hits` | 358.7 | 325.7 | +9.2% |

### 250,000 elements

| Scenario | Before ns/op | After ns/op | Reduction |
|---|---:|---:|---:|
| `pointer/lookup/i64/value8/hits` | 262.1 | 267.2 | -1.9% |
| `pointer/lookup/i64/value8/misses` | 347.6 | 338.8 | +2.5% |
| `pointer/lookup/i64/value8/mixed` | 320.5 | 313.2 | +2.3% |
| `pointer/lookup/i64/value8/churn` | 281.7 | 285.2 | -1.2% |
| `array/lookup/i64/value8/hits` | 235.4 | 170.7 | +27.5% |
| `array/lookup/i64/value8/misses` | 257.5 | 188.2 | +26.9% |
| `array/lookup/i64/value8/mixed` | 246.0 | 181.0 | +26.5% |
| `array/lookup/i64/value8/churn` | 249.7 | 180.6 | +27.7% |
| `array/lookup/i64/value8/ordered` | 123.0 | 128.6 | -4.5% |
| `stable-array/lookup/i64/value8/hits` | 250.4 | 185.3 | +26.0% |
| `stable-array/lookup/i64/value8/misses` | 277.2 | 205.9 | +25.7% |
| `stable-array/lookup/i64/value8/mixed` | 261.3 | 195.2 | +25.3% |
| `stable-array/lookup/i64/value8/churn` | 260.1 | 196.6 | +24.4% |
| `stable-array/lookup/i64/value8/ordered` | 138.0 | 129.7 | +6.0% |
| `split-array/lookup/i64/value8/hits` | 232.7 | 152.2 | +34.6% |
| `split-array/lookup/i64/value8/misses` | 245.2 | 167.6 | +31.6% |
| `split-array/lookup/i64/value8/mixed` | 242.0 | 160.6 | +33.6% |
| `split-array/lookup/i64/value8/churn` | 251.4 | 169.6 | +32.6% |
| `split-array/lookup/i64/value8/ordered` | 106.3 | 99.8 | +6.1% |
| `pointer/lookup/i64/value256/hits` | 494.6 | 492.0 | +0.5% |
| `array/lookup/i64/value256/hits` | 347.0 | 268.5 | +22.6% |
| `stable-array/lookup/i64/value256/hits` | 363.0 | 278.2 | +23.3% |
| `split-array/lookup/i64/value256/hits` | 322.2 | 159.8 | +50.4% |
| `pointer/lookup/string32/value8/hits` | 591.4 | 593.6 | -0.4% |
| `array/lookup/string32/value8/hits` | 589.0 | 507.5 | +13.8% |
| `stable-array/lookup/string32/value8/hits` | 604.5 | 543.4 | +10.1% |
| `split-array/lookup/string32/value8/hits` | 662.5 | 606.9 | +8.4% |

## Interpretation and limitations

The address-backed integer tree-descent paths show substantial elapsed-time
reductions in these runs. At 250,000 elements, small-value hit lookups improve
by about 26-35%; large-value hits improve by about 23% in ArrayBased and
StableArrayBased, and about 50% in SplitArrayBased. Fixed-width string-key hits
improve by about 8-14%. These are measurements on this compiler and machine,
not cross-platform guarantees.

Controls vary too. In particular, ordered ArrayBased lookup at 10,000 elements
has a 10% slower median even though the ordered-search algorithm is unchanged:
baseline samples span approximately 58-76 ns/op, candidate samples 66-76 ns/op.
Do not attribute small differences to the new descent loop or claim that every
scenario improves. Short small-tree timings are especially sensitive to system
and code-layout effects, even with fixed CPU affinity. Larger workloads and
other targets should be checked before making broad performance claims.

## Validation and reproduction

- 66/66 tests pass in Debug and ReleaseSafe.
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
