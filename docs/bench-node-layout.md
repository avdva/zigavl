# Array node layout experiment

Moving the balance factor from the nested key/value payload into the node lets
it share padding with the three 32-bit links. The tagged free-list slot and
pointer stability rules remain unchanged.

On x86_64, slots for `i64` keys and values shrink from 48 to 40 bytes in both
ArrayBased and StableArrayBased without subtree counts (16.7% less slot memory).
With subtree counts, slots remain 48 bytes. This measures slot size, not total
process memory or allocated capacity; savings depend on key/value alignment.

## Method

- Intel Core i7-12700H, 16 GB RAM, Linux x86_64, Zig 0.17.0, ReleaseFast.
- Baseline: `d4025f8`, including the merged updateKey fix and benchmark matrix.
- Candidate: only the array/stable-array node layout changes.
- 250,000 elements, deterministic insertion/query seeds, seven rounds.
- Before/after processes alternated order between rounds; no compilation or
  tests ran alongside the timed comparisons. A 10,000-element lookup run per
  binary preceded the main comparison and is excluded from the table.
- Each process rebuilt its trees. Values below are median ns/op. Lookup
  payloads are 8-byte arrays; insertion benchmarks use `i64` values.
- Filters: `array/lookup/i64/value8`, `insert/random`, `counted-random`.
  Substring matching also includes stable/split-array and delete-insert cases.

## Results

Positive reductions mean lower elapsed time.

| Scenario | Before ns/op | After ns/op | Reduction |
|---|---:|---:|---:|
| `array/lookup/i64/value8/hits` | 247.9 | 242.2 | +2.3% |
| `array/lookup/i64/value8/misses` | 272.1 | 259.8 | +4.5% |
| `array/lookup/i64/value8/mixed` | 261.2 | 252.2 | +3.4% |
| `array/lookup/i64/value8/churn` | 261.2 | 252.4 | +3.4% |
| `array/lookup/i64/value8/ordered` | 125.7 | 124.6 | +0.9% |
| `stable-array/lookup/i64/value8/hits` | 253.2 | 254.5 | -0.5% |
| `stable-array/lookup/i64/value8/misses` | 282.0 | 281.8 | +0.1% |
| `stable-array/lookup/i64/value8/mixed` | 277.3 | 266.6 | +3.9% |
| `stable-array/lookup/i64/value8/churn` | 271.2 | 265.4 | +2.1% |
| `stable-array/lookup/i64/value8/ordered` | 141.7 | 139.7 | +1.4% |
| `split-array/lookup/i64/value8/hits` | 231.1 | 232.2 | -0.5% |
| `split-array/lookup/i64/value8/misses` | 246.4 | 245.1 | +0.5% |
| `split-array/lookup/i64/value8/mixed` | 241.0 | 252.2 | -4.7% |
| `split-array/lookup/i64/value8/churn` | 247.5 | 255.2 | -3.1% |
| `split-array/lookup/i64/value8/ordered` | 102.3 | 108.8 | -6.3% |
| `pointer/insert/random` | 284.7 | 281.3 | +1.2% |
| `pointer/delete-insert/random` | 633.7 | 638.9 | -0.8% |
| `array/insert/random` | 301.6 | 284.0 | +5.8% |
| `array/delete-insert/random` | 592.5 | 570.8 | +3.7% |
| `stable-array/insert/random` | 314.5 | 310.4 | +1.3% |
| `stable-array/delete-insert/random` | 646.0 | 629.2 | +2.6% |
| `split-array/insert/random` | 273.1 | 274.2 | -0.4% |
| `split-array/delete-insert/random` | 581.5 | 587.6 | -1.0% |
| `pointer/insert/counted-random` | 290.8 | 291.0 | -0.1% |
| `array/insert/counted-random` | 340.5 | 337.1 | +1.0% |
| `stable-array/insert/counted-random` | 357.6 | 340.7 | +4.7% |
| `split-array/insert/counted-random` | 314.4 | 316.0 | -0.5% |

## Interpretation

The reliable gain is reduced slot memory. ArrayBased shows modest improvements
in lookup and insertion in this run. StableArrayBased is mostly similar or
slightly faster. Unchanged pointer/split-array controls also vary by several
percent, so these timings do not establish a universal speedup or statistical
significance. Further comparisons should include larger values and other
hardware before claiming a general throughput improvement.

To repeat, build each revision with `zig build install-bench -Doptimize=ReleaseFast`,
keep separate binaries, and alternate their runs with the same filters and
`--size=250000`. Collect at least seven samples per scenario; compare medians
and inspect control workloads alongside the changed backends.
