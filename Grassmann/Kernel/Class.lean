/-
Kernel dispatch (DESIGN.md §5.4): `class Kernels (V : TensorBundle)`.

Every typed operation of the algebra layer (`Grassmann.Algebra.*`) evaluates
through the `Kernels V` instance of its space: four operations, each generic in
the coefficient type and in the operand/result storage layouts,

| field | computes |
|---|---|
| `bin op la lb lc x y` | `op(x, y)`, every contribution landing in layout `lc` |
| `binProj op la lb lc x y` | the part of `op(x, y)` in `lc` (a grade projection) |
| `un op la lc x` | `op(x)` for a unary `op` |
| `unProj op la lc x` | the part of `op(x)` in `lc` |

Every field defaults to the reference plan kernels (`Grassmann.Kernel.refBin`,
...), and `Kernels.reference` is a **low-priority instance for every space**, so
`[Kernels V]` always resolves.

## Extension point (generated kernels)

A code generator (DESIGN.md §5.2, `basis!`/`grassmann_kernels`) adds a
*default-priority* instance for a concrete space that overrides the fields for
the shapes it has unrolled straight-line kernels for and delegates the rest to
the reference, e.g.

```lean
instance : Kernels ℝ3 where
  bin op la lb lc x y := match op, la, lb, lc with
    | .mul, .full, .full, .full => mulR3 x y          -- generated, @[specialize]
    | op, la, lb, lc => Grassmann.Kernel.refBin ℝ3 op la lb lc x y
```

Instance resolution prefers it over `Kernels.reference`. At a call site the
operation and layouts are literals (the typed instances pass constructor
applications), so after inlining the `match` constant-folds to the generated
kernel, and the kernel is specialized at the coefficient type like the
reference loops. Fields a generated instance does not mention keep their
reference defaults.
-/
import Grassmann.Kernel.Reference

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Kernel

/-- The product and linear-map kernels of the space `V`, generic in the
coefficient type and the storage layouts (DESIGN.md §5.4). -/
class Kernels (V : TensorBundle) where
  /-- `op(x, y)` from layouts `la × lb` into `lc`; every contribution must land in `lc`. -/
  bin : {α : Type} → [Coeff α] → BinOp → (la lb lc : Layout) →
      Values α (la.size V.n) → Values α (lb.size V.n) → Values α (lc.size V.n) :=
    fun op la lb lc x y => refBin V op la lb lc x y
  /-- The part of `op(x, y)` in layout `lc` (contributions outside it are dropped). -/
  binProj : {α : Type} → [Coeff α] → BinOp → (la lb lc : Layout) →
      Values α (la.size V.n) → Values α (lb.size V.n) → Values α (lc.size V.n) :=
    fun op la lb lc x y => refBinProj V op la lb lc x y
  /-- `op(x)` from layout `la` into `lc`. -/
  un : {α : Type} → [Coeff α] → UnOp → (la lc : Layout) →
      Values α (la.size V.n) → Values α (lc.size V.n) :=
    fun op la lc x => refUn V op la lc x
  /-- The part of `op(x)` in layout `lc`. -/
  unProj : {α : Type} → [Coeff α] → UnOp → (la lc : Layout) →
      Values α (la.size V.n) → Values α (lc.size V.n) :=
    fun op la lc x => refUnProj V op la lc x

/-- The reference kernels for every space (low priority: generated instances win). -/
instance (priority := low) Kernels.reference (V : TensorBundle) : Kernels V := {}

end Grassmann
