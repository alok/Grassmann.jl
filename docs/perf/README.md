# Performance dashboard

Performance is designed in and measured continuously, against the reference implementation:
every package has a benchmark suite, every Lean case has a Julia twin measured by the same
algorithm, every case has a budget (a maximum Lean/Julia ratio), and a guard flags regressions.

| file | what |
|---|---|
| [`latest.md`](latest.md) | the last full run: every case, Lean vs Julia, ratio, budget, status |
| [`history.jsonl`](history.jsonl) | one JSON record per recorded run (commit, machine, date, every case) |
| [`budgets.toml`](budgets.toml) | budget rules (first matching pattern wins) |
| [`../PERF.md`](../PERF.md) | the narrative log: findings, rules, summary table |

## Running

```sh
uv run scripts/bench/run.py                       # build, run Lean + Julia, compare, record
uv run scripts/bench/run.py --suite math --no-record
uv run scripts/bench/run.py --smoke --no-record   # seconds; checks that everything runs
uv run scripts/bench/run.py --guard               # exit 1 on a budget violation or regression
```

`run.py` runs `lake build bench`, then `lake exe bench --json .lake/bench/lean.json`, then one
Julia process per environment group (`oracle/bench/run.jl --include <suites>`), then
`scripts/bench/compare.py`. Julia environments: `--julia-env` (default `$GRASSMANN_JULIA_ENV`,
else `oracle/`) for everything except Dendriform and DeMorgan, which run in
`oracle/bench/env2` (`--julia-env2`; a copy of the environment the oracle generators use:
Dendriform conflicts with AbstractAnalysis). Geophysics.jl is included from its source,
`$CHAKRAVALA/Geophysics.jl` (default `~/chakravala`). The `fatou` suite runs with
`--threads=auto` (its `*_par` cases compare Lean tasks with Julia threads); every other suite
runs single-threaded.

The pieces can be run separately:

```sh
lake exe bench [--smoke] [--json out.json] [--filter substr]... [--samples n] [--sample-ms n] [suite ...]
julia --startup-file=no --project=<env> oracle/bench/<suite>.jl [same options]
uv run scripts/bench/compare.py --lean lean.json --julia julia.json [--julia more.json] [--guard] [--no-record]
```

## The harness

`Bench/Harness.lean` and `oracle/bench/harness.jl` implement the same algorithm:

1. **warm-up**: one untimed call (in Julia it compiles), then one timed call whose checksum is
   the reported `check`;
2. **calibration**: the batch size `k` grows ×4 until a batch takes a tenth of the sample
   target, then is scaled so a batch takes about `--sample-ms` (20 ms);
3. **samples**: 7 batches (fewer when one call is slow; a case is capped near 1.5 s), each
   giving ns per operation = batch time / (k · ops). **min** and **median** are reported; ratios
   and the guard use the min, the most stable estimator on a shared machine.

A case is `bench "name" (ops := n) (param := "n=…") fun i => body` (Lean) or
`bench!(i -> body, ctx, "name"; ops = n, param = "…")` (Julia). `ops` is the number of
logical operations one call performs, so every number is **ns per operation**. Keys are
`suite/case` and identical on both sides; `param` records the size.

**Checks.** Each body returns a value summarized by `Checksum` (a float is itself, an integer
its value, a string or collection its length). Both twins compute the same quantity from
identical inputs (SplitMix64 streams, `randFloats`/`randfloats`, or arithmetic sweeps), so
`compare.py` marks `=` when the checksums agree (rtol 1e-9) and `≠` when they differ, which
flags a benchmark that does different work, or a real semantic difference (e.g.
`directsum/blade_show_R10`: Lean prints `v₀` for generator 10 where Julia prints `v10`).

### Rules learned the hard way

* **`blackBox` must use its salt.** `@[noinline] def blackBox (_salt : Nat) (x : α) := x` is
  defeated by arity reduction: the compiler drops the unused salt, `f (blackBox s 10)` becomes
  a closed term evaluated once at start-up, and a body `fun s => …` that no longer mentions
  `s` is itself extracted (cases measured 0.005 ns). The harness's `blackBox` is implemented by
  a function whose result depends on the salt through a branch the compiler cannot decide.
* **Do not `blackBox` a structure of closures that must be specialized.** Passing Fatou's
  `Define` through `blackBox` made `fatou` run its generic, boxed kernel (25× slower). Salt the
  *size* instead and let the definition be inlined at the call site (`Bench/Fatou.lean`).
* **Checksums must be cheap.** `Nat.toFloat` of a value `≥ 2^53` takes the `Float.ofScientific`
  model path: ~8 µs for a 64-bit value, which swamped a 0.7 µs truth-table formula. Convert
  through `UInt64`.
* **Julia compiles on first call.** The warm-up's `@timed` excludes `compile_time` when deciding
  whether a case is too slow for a second warm-up call.
* **Julia hoists loop-invariant work.** Every body call goes through a call-site `@noinline`,
  and `blackbox(i, x)` hides literal inputs from constant propagation
  (`Base.compilerbarrier(:const, x)`).
* **Static sizes.** Suites write sizes the way user code would (`Values Float 3`,
  `Values{3,Float64}`), inlining helpers at literal dimensions.

## Result files

Both languages write the same schema:

```json
{"lang": "lean", "smoke": false, "sample_ns": 20000000, "samples": 7,
 "results": [
  {"key": "math/exp", "suite": "math", "case": "exp", "param": "n=10000", "ops": 10000,
   "iters": 300, "samples": 7, "min_ns": 6.61, "median_ns": 6.72, "max_ns": 6.74,
   "check": 6.749227492323128e304}
]}
```

(Julia adds `"julia"` and `"threads"`.) Non-finite numbers are `null`.

## Budgets and the guard

`budgets.toml` holds `default` (the target ratio for every case, 2×) and ordered
`[[budget]]` rules `{pattern, ratio?, max_ns?, note}`; the first rule whose shell pattern
matches a key applies. Known gaps are listed with the measured ratio plus headroom and a
diagnosis in `note`, so the debt is explicit and a further regression still fails; tightening a
budget after a fix is part of the fix.

`compare.py --guard` exits 1 when a case is over its budget or when its Lean minimum
regressed by more than `--threshold` (20%) against the previous history record of the same
machine (machine = CPU, core count, OS; no hostname). Smoke runs are never recorded or
guarded against.

## Adding a suite

1. `Bench/<Pkg>.lean`: `def suite : Suite := ⟨"<pkg>", do … bench … ⟩`; import it in
   `Bench.lean` and list it in `Bench/Main.lean`.
2. `oracle/bench/<pkg>.jl`: `include` the harness, define `suite_<pkg>(ctx)`, end with
   `register!("<pkg>", suite_<pkg>)` and the standalone `main_suites` line; add the suite to
   `JULIA_SUITES` in `scripts/bench/run.py`.
3. Use identical inputs and checks; run `uv run scripts/bench/run.py --suite <pkg> --no-record`
   until every check is `=`; add budget rules for the cases that are knowingly over 2×.
