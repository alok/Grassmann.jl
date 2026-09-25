# AGENTS.md: working on this repository

This repo ports Michael Reed's Julia ecosystem (Grassmann.jl and friends) to Lean 4. Start here:

1. `docs/DESIGN.md`: the architecture contract (types, kernels, notation, oracle, proofs).
2. `docs/port-notes/<package>.md`: exact Julia semantics with file:line citations and goldens.
   Read the relevant one before touching a module.
3. `docs/PERF.md`: measured performance facts. Add to it; don't guess.

Rules (details in DESIGN.md §2):
- Toolchain `leanprover/lean4:v4.35.0-rc3`. The root package has **no dependencies**.
- `lake build` must stay warning-free (CI uses `--wfail`); `lake test` runs all tests.
- No `sorry`, custom axioms or `native_decide` in library code.
- Float bulk data lives in `StaticVectors.Values` / `FloatArray`, never `Array Float`.
- Hot Float loops are tail-recursive; no `for`/`break` with mutable Floats.
- Generic kernels take one bundled class instance and are `@[specialize]`.
- Julia is the oracle: `oracle/` regenerates goldens (`julia --startup-file=no --project=oracle ...`).
  Documented Julia defects live in `oracle/defects.toml`; we fix them rather than replicate them.
- Atomic commits (`area: summary`), each one building green.
- Use `rg`/`fd`, not `grep`/`find`. Python tooling runs through `uv run`.
