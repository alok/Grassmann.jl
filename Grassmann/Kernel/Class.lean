/-
Kernel dispatch (DESIGN.md §5.4): `class Kernels (V : TensorBundle)`.

Every typed operation of the algebra layer (`Grassmann.Algebra.*`) evaluates
through the `Kernels V` instance of its space, generic in the coefficient type and
in the operand/result storage layouts:

| field | computes |
|---|---|
| `bin op la lb lc x y` | `op(x, y)`, every contribution landing in layout `lc` |
| `binProj op la lb lc x y` | the part of `op(x, y)` in `lc` (a grade projection) |
| `un op la lc x` | `op(x)` for a unary `op` |
| `unProj op la lc x` | the part of `op(x)` in `lc` |
| `add l x y`, `sub l x y`, `neg l x` | `x + y`, `x - y`, `-x` in layout `l` (Julia `+`/`-` of one container kind) |
| `smul l s x`, `muls l x s` | `s·xᵢ`, `xᵢ·s` (scalar multiples, the scalar on its own side) |
| `conv la lc x` | `x` re-indexed from layout `la` into `lc` (Julia's container conversions and grade projections: `Multivector(t)`, `even(m)`, `m(g)`) |
| `convAdd la lb lc x y`, `convSub …` | `conv la lc x ± conv lb lc y` (Julia `+`/`-` of two container kinds, promoted) |

Every field defaults to the reference implementation (the interpreted plans
`Grassmann.Kernel.refBin`, ..., `Values` arithmetic and `convertLayout`), and
`Kernels.reference` is a **low-priority instance for every space**, so `[Kernels V]`
always resolves.

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

The linear fields (`add` … `convSub`) compute exactly what the reference computes, with the
same floating-point operations: a sum of two containers of different kinds adds explicit
zeros (`xᵢ + 0`), as the promoted sum of the reference does, so the sign of a zero agrees.
-/
module

public import Grassmann.Kernel.Reference

@[expose] public section

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
  /-- `x + y` in layout `l` (Julia `+` of two containers of one kind, `SV/linalg.jl:14`). -/
  add : {α : Type} → [Coeff α] → (l : Layout) →
      Values α (l.size V.n) → Values α (l.size V.n) → Values α (l.size V.n) :=
    fun _ x y => x + y
  /-- `x - y` in layout `l`. -/
  sub : {α : Type} → [Coeff α] → (l : Layout) →
      Values α (l.size V.n) → Values α (l.size V.n) → Values α (l.size V.n) :=
    fun _ x y => x - y
  /-- `-x` in layout `l`. -/
  neg : {α : Type} → [Coeff α] → (l : Layout) → Values α (l.size V.n) → Values α (l.size V.n) :=
    fun _ x => -x
  /-- `s·xᵢ` for every coefficient (the scalar on the left, Julia `s * t`,
  `src/products.jl:830-851`). -/
  smul : {α : Type} → [Coeff α] → (l : Layout) → α → Values α (l.size V.n) → Values α (l.size V.n) :=
    fun _ s x => x.map (s * ·)
  /-- `xᵢ·s` for every coefficient (the scalar on the right, Julia `t * s`). -/
  muls : {α : Type} → [Coeff α] → (l : Layout) → Values α (l.size V.n) → α → Values α (l.size V.n) :=
    fun _ x s => x.map (· * s)
  /-- `x` re-indexed from layout `la` into `lc` (`convertLayout`: zeros where `la` lacks a blade,
  blades `lc` lacks dropped). -/
  conv : {α : Type} → [Coeff α] → (la lc : Layout) → Values α (la.size V.n) → Values α (lc.size V.n) :=
    fun la lc x => convertLayout V.n la lc x
  /-- `conv la lc x + conv lb lc y` (Julia `+` of two element kinds, promoted to `lc`). -/
  convAdd : {α : Type} → [Coeff α] → (la lb lc : Layout) →
      Values α (la.size V.n) → Values α (lb.size V.n) → Values α (lc.size V.n) :=
    fun la lb lc x y => convertLayout V.n la lc x + convertLayout V.n lb lc y
  /-- `conv la lc x - conv lb lc y`. -/
  convSub : {α : Type} → [Coeff α] → (la lb lc : Layout) →
      Values α (la.size V.n) → Values α (lb.size V.n) → Values α (lc.size V.n) :=
    fun la lb lc x y => convertLayout V.n la lc x - convertLayout V.n lb lc y

/-- The reference kernels for every space (low priority: generated instances win). -/
instance (priority := low) Kernels.reference (V : TensorBundle) : Kernels V := {}

end Grassmann
