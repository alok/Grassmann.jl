# Grassmann.lean

A Lean 4 port of [Michael Reed](https://github.com/chakravala)'s Julia ecosystem for
⟨Grassmann-Clifford-Hodge⟩ differential geometric algebra:
[Grassmann.jl](https://github.com/chakravala/Grassmann.jl) and the packages around it
(DirectSum, Leibniz, AbstractTensors, StaticVectors, Cartan, MeshTopology, Adapode, Fatou,
UnitSystems, Similitude, and more).

> **Status: under active construction.** This branch is a hard cutover from the earlier
> experimental port (preserved on the `archive/*` branches). See [`docs/DESIGN.md`](docs/DESIGN.md)
> for the architecture and [`docs/port-notes/`](docs/port-notes/) for the per-package specs.

## Design in one paragraph

Spaces are values (`ℝ^3`, `S!"-+++"`, `D!"0,1,1,1"`, `S!"∞∅+++"`). Element types are indexed by
the space and, where it's free, by grade or parity: `Chain V 2 Float`, `Spinor V Float`,
`Multivector V Rat`. Wedging a `Chain V a` with a `Chain V b` produces a `Chain V (a+b)`, checked
by the type checker and erased at runtime. Products are unrolled straight-line kernels generated at
elaboration time for each registered algebra, Lean's analogue of Julia's `@generated`. Specialized
at `Float`, they run on unboxed `FloatArray`s at Julia speed ([`docs/PERF.md`](docs/PERF.md)). A
dynamic layer reproduces Julia's runtime result types and printing exactly. The Julia packages
serve as the test oracle: [`oracle/`](oracle/) pins them and commits JSON goldens.

## Build

```bash
lake build        # all libraries (no external dependencies)
lake test         # unit, golden (Julia oracle) and property tests
lake exe bench    # benchmarks
```

Toolchain: `leanprover/lean4:v4.35.0-rc3`. Plots are rendered with
[LeanPlot](https://github.com/alok/LeanPlot) in the `gallery/` sub-package.

## Credit and licence

The mathematics, API design and naming are Michael Reed's; cite his work (see
[`CITATION.cff`](CITATION.cff)) when you use this. As a port of AGPL-3.0 software, this
repository is licensed under the [GNU AGPL v3](LICENSE).
