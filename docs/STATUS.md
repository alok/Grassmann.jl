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
   - set up CI (Linux) at the end.

Open question for Alok: should the port move to a standalone repo (suggested
`alok/Grassmann.lean`) instead of this Grassmann.jl fork?
