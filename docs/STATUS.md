# Status and resume notes (paused 2026-09-25 ~10:30 PDT)

The work was paused to save tokens. All agents are stopped. Nothing is lost: every agent's work
is committed on its own local branch (an unfinished tail is snapshotted as a `wip:` commit). The
`wip:` commits may not build and may contain scratch files (for example `dbg.lean`, `p1.lean`
at the worktree root): drop those files when merging.

## On master (pushed, `origin/master`)

- **Tests:** `lake build` is warning-free. `lake test` passes 3,451,655 checks in 27 suites:
  - the 24 older suites, 3,197,242 checks;
  - Clifford, 36;
  - FlowGeometry, 253,359;
  - Adapode, 1,018.
- **Benches:** `lake exe bench` has 17 suites, each with a Julia twin. `adapode` runs in its
  own Julia process (see `scripts/bench/run.py`).
- **Merged today:**
  - parity wave 1: foundations, dynamic API, calculus/composite/forms, fusion and batching,
    Cartan element/spectral/solvers, plotting, misc, units;
  - FlowGeometry;
  - the Adapode ODE solvers. They are bit-exact against the Julia goldens. RK4 and adaptive
    Dormand–Prince run 13–17× faster than Julia; Heun and ABM4 run 1.2–2× slower.
- **Specs:** `docs/DSL.md` is the draft spec for the interactive DSL (`ga!{…}`, `#ga`,
  `lake exe ga`).
- **Not re-measured:** the full Lean-vs-Julia sweep (`uv run scripts/bench/run.py`) has not
  been rerun since wave 1. Run it on a quiet machine.

## Paused work (local branches, worktrees under `.claude/worktrees/`)

Parity wave 2 (script:
`~/.claude/projects/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/workflows/scripts/parity-wave-2-wf_174a1009-1f5.js`).
Each agent owns a disjoint area; the ownership and gap text are in that script.

| # | branch `worktree-wf_174a1009-1f5-N` | area | state at pause |
|---|---|---|---|
| 1 | …-1 | Adapode FEM/PDE + `Cartan/Solve` | 5 commits + wip. Done: flat P1 assembly (bit-exact), Dirichlet/Poisson/Robin/transport/heat/wave/bistable solvers, CR-P0 Stokes, elasticity, DG Poisson, Nedelec Maxwell, Chorin Navier–Stokes, banded LU. Spectral PDE solvers not started |
| 2 | …-2 | foundations API | 9 commits + wip. Done: Dendriform uses the AbstractLattices ∨ (Graft notation dropped), χ/count_gdims in Leibniz, naming registry, `@basis`/`@dualbasis`/`@mixedbasis`, Base methods on terms, one set of kind predicates + Notation re-exports, universal `I`, interop, DiagonalForm printing, Leibniz index tables |
| 3 | …-3 | dynamic layer + docs corpus | 7 commits + wip. Done: Cayley tables, space set ops, real-angle phasors, V(∇) and ∂/d/δ, simplicial complexes, chainfield, matrices/linear maps/closures in the interpreter, tangent products with derivation coefficients. Unimplemented-docs count not re-measured |
| 4 | …-4 | generated-kernel perf | 4 commits + wip. Done: inline stores in interpreted plans, linear kernels, fused `R*x*~R`, compiled dynamic loops, exclusive output buffers, allocation-floor bench |
| 5 | …-5 | values/composite/forms perf | 0 commits + wip only (read carefully before merging) |
| 6 | …-6 | JuliaBase math perf | 2 commits + wip. Done: inline bit casts, literal-sized tables; exp/log/sin/cos/tan/asin at or below Julia; leaf kernels for sinh/tanh/atan2 |
| 7 | …-7 | Cartan core perf + MeshTopology | 6 commits, clean. Done: radix-4/8 FFT, prepared Grid2Eval/Grid3Eval in Cartan, direct-connectivity mesh kernels, pairwise sum (0.094 vs Julia 0.087 ns), MeshTopology degrees/edges. Delaunay mesher not started |
| 8 | …-8 | units, misc, defects, docs | 6 commits + wip. Done: wave-1 Julia defects in `defects.toml`, honest README perf claims, DESIGN §5.5, PERF.md facts, Wilkinson errval register program, AbstractAnalysis bench + twin, UnitSystems perf, budgets |
| 9 | …-9 | LeanPlot + gallery | 3 commits, clean. LeanPlot `next` (pushed, `1c9f273`) has contour labels, custom scales, the volume mark and continuation-passing streamplots; the gallery has himmelblau, heatmap_logscale and the volume figures |

Also paused: **Cartan Diffgeo + Grid**, on branch `worktree-wf_94031bbb-b39-3`. It has 20 commits
plus a wip commit, covering the grid.jl calculus, curves, surfaces, curvature and Christoffel
symbols, all with Lean and Julia benchmarks. It is based on the old master `0ac54fdd`, so expect
merge conflicts in Cartan roots and registrations.

## How to resume

1. Check that the main checkout is on master: `git branch --show-current`. The user's launchd
   `claude-daemon` (03:00 and 15:00) once switched it to its own branch.
   `scripts/merge-branch.sh` refuses to run off master.
2. For each branch above:
   - finish or merge it with `scripts/merge-branch.sh <branch> "merge: …"`;
   - fix any combined-build breakage;
   - run `lake build` and `lake test`;
   - push;
   - `git worktree remove --force` the worktree.

   To continue an unfinished area, start a fresh agent in that worktree with its
   ownership/gap text from the wave-2 script. Tell it to begin from its branch's log and
   its `wip:` commit (amend or split that commit).
3. Add registrations that agents requested but may not make themselves: `Tests.lean`,
   `Tests/Main.lean`, `Bench.lean`, `Bench/Main.lean`, `scripts/bench/run.py`, and the
   package roots.
4. New worktrees: run `cp -Rc <main>/.lake .lake` first. It is an APFS copy-on-write clone
   that is up to date and costs about 0 disk. Disk is tight (about 5 GB free at pause).
5. Then:
   - rerun the full bench sweep;
   - re-audit `docs/parity-gaps.json`, whose statuses were not updated after wave 1;
   - start the "exceed Julia" phase (perf, GPU in an optional `accel/` package, proofs);
   - build the DSL (`docs/DSL.md`);
   - ~~set up CI (Linux)~~ done 2026-10-28: CI runs on every push to master and on PRs,
     green on Linux (the libm `atanh` mismatch is fixed by using Julia's kernel).

Also landed 2026-10-28 from a cloud session (on GitHub, not yet on the Mac): the plan
interpreter proof (`Grassmann.Proofs.Interp`) and `docs/TALK.md`. Pull master before
merging the wave-2 branches.

Open question for Alok: should the port move to a standalone repo (suggested
`alok/Grassmann.lean`) instead of this Grassmann.jl fork?

## Cloud session 2026-11-04 (branch `claude/tests-docs-audit`)

Work done off `origin/master` (`21581c6`) from a Linux cloud container, deliberately outside
the areas the paused wave-2 branches own, so merging those should not conflict beyond the
suite registrations in `Tests/Grassmann.lean`, `Tests/Dynamic.lean`, `Tests/AbstractAnalysis.lean`
and `Clifford.lean`.

- **Baseline:** `lake build` warning-free (1180 jobs, 14 min on 4 cores); `lake test` 3,453,355
  checks, 0 failed, 56 s.
- **`docs/parity-gaps.json` re-audited:** the 134 non-performance entries were re-checked
  against the code at `21581c6` (read-only: definitions and `Tests/` uses, cited as
  `file:line`). Each audited entry now has an `audit` object (`was`, `evidence`, `remaining`).
  Statuses: 60 DONE, 63 PARTIAL, 13 MISSING; the 66 `performance` rows (SLOW/UNMEASURED) were
  not re-measured (no Julia here). Spot checks found the audit sometimes calls a thing
  untested when a test exists under another name (`JNum.rpow` is tested as `^1//2`; the
  `N₂ … H₂` aliases exist): treat `remaining` as a lead, not a verdict.
- **New tests:** `grassmann/identities` (trace property of `⟨⟩₀`, antisymmetrised products,
  even/odd and grade decompositions, the left-contraction derivation rule, `antisandwich`,
  `pseudograde`), `dynamic/anti` (`antisandwich(I, x) = x`, `isfinite`), compile-time checks
  of AbstractAnalysis function families and countable arrays (`Tests/AbstractAnalysis/Families.lean`).
  No library bug surfaced. One non-identity is worth knowing: Julia's `>>>` projects onto the
  grades of the *kind* of `x`, and complements can change the kind (in `CGA3`
  `⋆ʳ⋆ˡ(1 + 2v∞∅₁₂)` is a `Spinor`, as the unary goldens confirm), so
  `antisandwich(⋆ˡR, ⋆ˡx) = ⋆ˡ(R >>> x)` holds for chains but not for every dynamic pair.
- **Clifford sparse products:** `Clifford.Products` adds `*`, `∧`, `∨`, `⋅`, `⨼` on
  `MultiGrade`, evaluated on the stored terms only (`O(p·q)` blade pairs, independent of `2ⁿ`),
  tested against the dense kernels in ℝ3–ℝ5, STA, PGA3, CGA3 and by hand in `ℝ^16`.
- **Docs corpus gaps:** `scripts/docs_unimplemented.lean` lists the docs statements the docs
  evaluator does not model, with the reason (`lake test` prints only the count). At
  `21581c6`: 122 statements, led by `cayley` (31), `∂` (5), operators (5), `skeleton` (4),
  `barycenter` (4), `inv` (5) and number/element products with unsupported kinds (8). Most of
  these are wave-2 branch 3's area (Cayley tables, calculus, simplicial complexes, chain
  fields), so they were left alone here.
- **Follow-up (same branch):**
  - Cayley tables. `CayleyTable.showJulia` reproduces Julia's `show` of `cayley(V, op)`: the
    columns are tensors over the right operand, a column whose `Σ ⟨e ~e⟩₀` is zero is
    skipped, and a negative sum is Julia's `DomainError`. The docs evaluator runs
    `cayley`, and all 31 `algebra.md:626` goldens pass, so the unimplemented docs
    statements drop from 122 to 95. This touches wave-2 branch 3's area (Cayley tables), but
    only in `Forms/Show.lean` and the docs evaluator.
  - Runtime metrics (`f(t, g)`). `Grassmann.Algebra.Metric` takes a Gram matrix, which may
    be non-diagonal, and evaluates the products by Chevalley recursion. With the space's own
    metric it equals the kernels in every non-dyadic props space, CGA3's `g(∞, ∅) = −1`
    included. For `g = PᵀDP` it commutes with the outermorphism of `P`.
  - Element FFTs: `Cartan.Spectral.Elements`.
  - Planar exact-predicate Delaunay and convex hull: `Cartan.Delaunay`.
