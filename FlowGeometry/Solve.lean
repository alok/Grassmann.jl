import Grassmann
import FlowGeometry.Param

/-!
# Small linear solves by Cramer's rule with exterior products

FlowGeometry.jl computes every coefficient vector of its profiles (the NACA 4-digit camber
halves, the `Thickness` and `Modified` thickness polynomials) as
`transpose(Chain(rows…)) \ Chain(rhs…)`, which Grassmann.jl solves by Cramer's rule written with
wedge products (`Grassmann.jl src/composite.jl:706-736`, `Cramer` and `\`):

```
x₁, y₁ = t[1], t[end]
xᵢ₊₁ = xᵢ ∧ t[1+i],  yᵢ₊₁ = t[end-i] ∧ yᵢ          (i = 1 … N-1, N = M - 1)
det  = (t[1] ∧ y_N)[1]
out  = (v ∧ y_N,  xᵢ ∧ v ∧ y_{N-i} (i = 1 … N-1),  x_N ∧ v)
a    = Real.(out) ./ det
```

where `t[j]` are the *columns* of the matrix whose rows were given. The port evaluates the same
wedges with the Grassmann port's kernels (`ℝ3`, `ℝ4` generated, `ℝ5` reference plans), which round
exactly as Julia's generated code does: every coefficient golden
(`oracle/golden/flowgeometry/internals.json`) matches bit for bit. A singular system (the front
half of NACA `00xx`) gives `NaN`/`±Inf` coefficients, as Julia's does, and never throws.
-/

namespace FlowGeometry

open Grassmann DirectSum StaticVectors

/-- A vector of `ℝⁿ` from its coordinates (Julia `Chain{ℝn,1}(xs…)`). -/
@[inline] def vecOf {V : TensorBundle} (xs : Array Float) : Chain V 1 Float :=
  Chain.ofFn fun i => xs[i.1]!

/-- The top-grade coefficient of a chain (Julia `Real(x)` / `x[1]` of an `n`-vector). -/
@[inline] def top {V : TensorBundle} {G : Nat} (c : Chain V G Float) : Float := c.v.get! 0

/-- Column `j` of the matrix with the given rows (Julia `transpose(Chain(rows…))[j+1]`). -/
@[inline] def column {V : TensorBundle} (rows : Array (Array Float)) (j : Nat) : Chain V 1 Float :=
  vecOf (rows.map (·[j]!))

/-- Julia `transpose(Chain{ℝ3,1}(r₁, r₂, r₃)) \ Chain{ℝ3,1}(b)` (`composite.jl:722-736`, `N = 2`). -/
def solve3 (rows : Array (Array Float)) (b : Array Float) : Array Float :=
  let t1 : Chain ℝ3 1 Float := column rows 0
  let t2 : Chain ℝ3 1 Float := column rows 1
  let t3 : Chain ℝ3 1 Float := column rows 2
  let v : Chain ℝ3 1 Float := vecOf b
  let x2 : Chain ℝ3 2 Float := t1 ∧ t2
  let y2 : Chain ℝ3 2 Float := t2 ∧ t3
  let det := top (t1 ∧ y2 : Chain ℝ3 3 Float)
  let o1 := top (v ∧ y2 : Chain ℝ3 3 Float)
  let o2 := top (((t1 ∧ v : Chain ℝ3 2 Float) ∧ t3) : Chain ℝ3 3 Float)
  let o3 := top (x2 ∧ v : Chain ℝ3 3 Float)
  #[o1 / det, o2 / det, o3 / det]

/-- Julia `transpose(Chain{ℝ4,1}(r₁, …, r₄)) \ Chain{ℝ4,1}(b)` (`N = 3`). -/
def solve4 (rows : Array (Array Float)) (b : Array Float) : Array Float :=
  let t1 : Chain ℝ4 1 Float := column rows 0
  let t2 : Chain ℝ4 1 Float := column rows 1
  let t3 : Chain ℝ4 1 Float := column rows 2
  let t4 : Chain ℝ4 1 Float := column rows 3
  let v : Chain ℝ4 1 Float := vecOf b
  let x2 : Chain ℝ4 2 Float := t1 ∧ t2
  let y2 : Chain ℝ4 2 Float := t3 ∧ t4
  let x3 : Chain ℝ4 3 Float := x2 ∧ t3
  let y3 : Chain ℝ4 3 Float := t2 ∧ y2
  let det := top (t1 ∧ y3 : Chain ℝ4 4 Float)
  let o1 := top (v ∧ y3 : Chain ℝ4 4 Float)
  let o2 := top (((t1 ∧ v : Chain ℝ4 2 Float) ∧ y2) : Chain ℝ4 4 Float)
  let o3 := top (((x2 ∧ v : Chain ℝ4 3 Float) ∧ t4) : Chain ℝ4 4 Float)
  let o4 := top (x3 ∧ v : Chain ℝ4 4 Float)
  #[o1 / det, o2 / det, o3 / det, o4 / det]

/-- Julia `transpose(Chain{ℝ5,1}(r₁, …, r₅)) \ Chain{ℝ5,1}(b)` (`N = 4`). -/
def solve5 (rows : Array (Array Float)) (b : Array Float) : Array Float :=
  let t1 : Chain ℝ5 1 Float := column rows 0
  let t2 : Chain ℝ5 1 Float := column rows 1
  let t3 : Chain ℝ5 1 Float := column rows 2
  let t4 : Chain ℝ5 1 Float := column rows 3
  let t5 : Chain ℝ5 1 Float := column rows 4
  let v : Chain ℝ5 1 Float := vecOf b
  let x2 : Chain ℝ5 2 Float := t1 ∧ t2
  let y2 : Chain ℝ5 2 Float := t4 ∧ t5
  let x3 : Chain ℝ5 3 Float := x2 ∧ t3
  let y3 : Chain ℝ5 3 Float := t3 ∧ y2
  let x4 : Chain ℝ5 4 Float := x3 ∧ t4
  let y4 : Chain ℝ5 4 Float := t2 ∧ y3
  let det := top (t1 ∧ y4 : Chain ℝ5 5 Float)
  let o1 := top (v ∧ y4 : Chain ℝ5 5 Float)
  let o2 := top (((t1 ∧ v : Chain ℝ5 2 Float) ∧ y3) : Chain ℝ5 5 Float)
  let o3 := top (((x2 ∧ v : Chain ℝ5 3 Float) ∧ y2) : Chain ℝ5 5 Float)
  let o4 := top (((x3 ∧ v : Chain ℝ5 4 Float) ∧ t5) : Chain ℝ5 5 Float)
  let o5 := top (x4 ∧ v : Chain ℝ5 5 Float)
  #[o1 / det, o2 / det, o3 / det, o4 / det, o5 / det]

end FlowGeometry
