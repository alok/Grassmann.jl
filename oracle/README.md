# Julia oracle

Goldens for the Lean port, generated from the registered Julia packages. The Lean tests
(`Tests/Golden/*`, DESIGN.md §7) read the JSON files under `oracle/golden/` and compare element
kinds, coefficient vectors and printed strings.

**The file format is specified in [`docs/port-notes/oracle-schema.md`](../docs/port-notes/oracle-schema.md)**
(spaces, scalar encoding, element objects, every suite's case records, the defect table and the
comparison rules). This README covers generating and maintaining the files.

| path | what |
|---|---|
| `Project.toml`, `Manifest.toml` | pinned Julia environment ([Pinned versions](#pinned-versions)) |
| `common.jl` | JSON writer, space registry, element encoders, sample generators, defect matcher |
| `run_suite.jl` | runs one suite (all shards or named ones) in the current process |
| `generate_all.jl` | runs every shard in a fresh process, in parallel, then writes the manifests and `golden/defects.json` |
| `suites/*.jl` | one file per suite: `shards()` and `build(shard, defects)` |
| `docs/*.txt` | source of the `docs` suite (README/docs examples and probes) |
| `defects.toml` | known Julia defects with match patterns; the generator tags matching cases |
| `validate.py` | independent schema checker for the goldens (`uv run oracle/validate.py`) |
| `golden/<suite>.json` | suite manifest: shard list, case counts, totals |
| `golden/<suite>/<shard>.json` | the cases |
| `golden/defects.json` | `defects.toml` as JSON (policies and match tables), so consumers need no TOML parser |
| `golden/blades/*.jsonl` | older blade-level (Cayley table) goldens, format in `docs/port-notes/grassmann-parity.md` §9; written by `probes/parity/dump_all.jl`, not by these scripts |
| `golden/<pkg>/` (`dendriform`, `demorgan`, `primitivebits`, ...) | goldens of other packages, from their own generators under `oracle/<pkg>/` |
| `probes/` | one-off probe scripts from the port-notes survey |

## Suites

| suite | shards | cases | content |
|---|---|---|---|
| `construct` | 18 (every registry space) | ~1 200 | every element kind built from Julia source: native storage, dense vector, `show`, compact `show`, type |
| `arith` | 11 | ~21 000 | `+`/`-` over every ordered pair of kinds (the representation lattice), unary minus, scalar `* / //` |
| `products` | 10 | ~75 000 | 14 binary products over every ordered pair of kinds |
| `unary` | 15 | ~10 500 | 24 unary maps (involutions, complements, metric maps, projections, norms) and `grade(a, k)` |
| `composite` | 5 | ~1 200 | exp, log, sqrt, trig, hyperbolic, inv, powers, division on Float elements (with tolerances) |
| `floats` | 1 | ~20 400 | Julia `show`/compact `show` of Float64 (exact bits), Int64, Rational, Complex, Bool |
| `docs` | 58 | ~500 | the README/docs examples (grassmann-docs.md §6), REPL display and value |

Every Julia error and every mismatch against the generator's independent reference is attributed
to an entry of `defects.toml`; the manifests' `totals.unexplained` is 0.

## Regenerating

```sh
julia --startup-file=no --project=oracle -e 'using Pkg; Pkg.instantiate()'   # once
julia --startup-file=no --project=oracle oracle/generate_all.jl --jobs 12     # everything
julia --startup-file=no --project=oracle oracle/generate_all.jl products:E3 arith   # a subset
julia --startup-file=no --project=oracle oracle/generate_all.jl --retag       # after editing defects.toml
julia --startup-file=no --project=oracle oracle/generate_all.jl --list        # suites and shards
uv run oracle/validate.py                                                     # check the result
```

* Always pass `--startup-file=no`.
* `generate_all.jl` runs each `(suite, shard)` in its own `julia` process with the same project as
  itself. That is required, not an optimisation: Julia's regressive/interior caches are keyed
  without the tangent parameters, so one space can read entries cached by another
  (`defects.toml`: `cache-key-collision`).
* A full run takes about 25 minutes of wall time with 12 workers; `products` dominates.
  Shard logs go to a temporary directory whose path is printed on failure.
* `--retag` only re-applies `defects.toml` to the existing shard files (tags and stats) and
  rewrites the manifests and `golden/defects.json`. It takes seconds.
* Output is deterministic. Seeds come from a fixed hash of `"grassmann-oracle/<suite>/<shard>"`
  (recorded in `meta.seed_key`/`meta.seed`), and the files contain no timestamps. A rerun on the
  pinned environment reproduces the files byte for byte. A different Julia version may change the
  random streams (`Random.Xoshiro`), and so the sampled inputs.
* The exit status is non-zero if any shard fails. `generate_all.jl` re-parses every file it writes
  with JSON.jl; `validate.py` then checks the schema (field presence per kind, coefficient
  grammar, storage patterns, dense order, stats recount, file sizes ≤ 4 MiB, `unexplained` = 0).

## Pinned versions

Julia 1.13.0. The packages come from `Manifest.toml`: Grassmann 0.8.46, AbstractTensors 0.8.11,
DirectSum 0.8.21, Leibniz 0.3.0, StaticVectors 1.0.9, JSON 1.9.0. The port notes say which
master-branch files differ from these; the `src` files that matter here are byte-identical.
Every golden records the versions in `meta.julia` and `meta.packages`.

## Maintaining

* **A new Julia defect** (a nonzero `unexplained` after a regeneration): find the root cause, add
  a `[[defect]]` to `defects.toml` (the header comment specifies the fields and the match
  language; `docs/port-notes/oracle-schema.md` §10 is the consumer-side description), then
  `generate_all.jl --retag`. One entry per root cause; `source` cites Julia file:line.
* **A new sample or op**: edit `common.jl` (samples, `BINARY_OPS`/`UNARY_OPS`) or the suite
  file, regenerate the affected suites, and update the schema document in the same commit.
* **A format change**: bump `SCHEMA_VERSION` in `common.jl` and the schema document, and update
  `validate.py`.
* **A new suite**: add `suites/<name>.jl` with `shards()` and `build(shard, defects)` (return the
  shard object after `retag!`), and list it in `SUITES` in `generate_all.jl`.
* Keep every shard under 4 MiB: split by space or by op rather than growing a file.
