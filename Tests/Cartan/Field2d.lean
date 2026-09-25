import Tests.Cartan.Common

/-!
# The lifted algebra on a 2-D grid (`oracle/golden/cartan/field2d.json`)

Julia (the generator's inputs):

```julia
g2 = TensorField(ProductSpace(0:0.5:1.5, 0:0.25:1))
a = (x -> x[1] + 2x[2]).(g2);   b = (x -> 1 + x[1]*x[2]).(g2)
v = (x -> Chain(x[1], x[2], 1.0)).(g2);   w = (x -> Chain(1.0, -x[2], x[1])).(g2);   q = v*w
```

Every operation is compared bit for bit, except the `libm` functions (`sin`, `cos`, `tanh`,
`atan`), which allow 2 ulps.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann

namespace Tests.CartanTests.Field2d

/-- The grid `(0:0.5:1.5) ⊕ (0:0.25:1)`. -/
def ps : ProductSpace 2 := .ofAxes #v[Axis.colon 0 0.5 1.5, Axis.colon 0 0.25 1]
/-- Its open grid bundle. -/
abbrev g : GridBundle 2 (AffinePoint 2) := GridBundle.ofSpace ps
/-- Julia `g2 = TensorField(ProductSpace(…))`. -/
def g2 : TensorField g (AffinePoint 2) := TensorField.ofSpace ps
/-- Julia `a = (x -> x[1] + 2x[2]).(g2)`. -/
def a : TensorField g Float := g2.map fun x => x.get! 0 + 2 * x.get! 1
/-- Julia `b = (x -> 1 + x[1]*x[2]).(g2)`. -/
def b : TensorField g Float := g2.map fun x => 1 + x.get! 0 * x.get! 1
/-- A Julia `Chain(x, y, z)` of `ℝ3`. -/
def chain3 (x y z : Float) : Chain ℝ3 1 Float := Chain.ofFn fun i => #[x, y, z][i.1]!
/-- Julia `v = (x -> Chain(x[1], x[2], 1.0)).(g2)`. -/
def v : TensorField g (Chain ℝ3 1 Float) := g2.map fun x => chain3 (x.get! 0) (x.get! 1) 1
/-- Julia `w = (x -> Chain(1.0, -x[2], x[1])).(g2)`. -/
def w : TensorField g (Chain ℝ3 1 Float) := g2.map fun x => chain3 1 (-x.get! 1) (x.get! 0)
/-- Julia `q = v*w` (a quaternion field). -/
def q : TensorField g (Spinor ℝ3 Float) := v * w

/-- The golden operations with their `libm` tolerance. -/
def ops : List (String × FieldOut × Tol) :=
  let two : Float := 2
  let three : Float := 3
  let one : Float := 1
  [("g2", out g2, exact), ("a", out a, exact), ("b", out b, exact), ("v", out v, exact),
   ("w", out w, exact), ("a+b", out (a + b), exact), ("a-b", out (a - b), exact),
   ("a*b", out (a * b), exact), ("a/b", out (a / b), exact), ("2a", out (two * a), exact),
   ("a/3", out (a / three), exact), ("-a", out (-a), exact), ("a+1", out (a + one), exact),
   ("1-a", out (one - a), exact), ("sin(a)", out a.sin, libm), ("cos(a)", out a.cos, libm),
   ("exp(a)", out a.exp, exact), ("log(b)", out b.log, exact), ("sqrt(b)", out b.sqrt, exact),
   ("b^0.5", out (b.pow 0.5), exact), ("b^2", out (b.powInt 2), exact),
   ("b^-3", out (b.powInt (-3)), exact), ("cbrt(b)", out b.cbrt, exact), ("tanh(a)", out a.tanh, libm),
   ("atan(a)", out a.atan, libm), ("inv(b)", out b.invF, exact), ("abs(a-1)", out (a - one).abs, exact),
   ("sign(a-1)", out (a - one).sign, exact), ("max(a,1)", out (a.maxF 1), exact),
   ("min(a,1)", out (a.minF 1), exact), ("mod(a,0.75)", out (a.mod 0.75), exact),
   ("rem(a,0.75)", out (a.rem 0.75), exact), ("round(a*1.3)", out (a * (1.3 : Float)).round, exact),
   ("iszero(a)", out a.iszero, exact), ("graph(a)", out a.graph, exact),
   ("v+w", out (v + w), exact), ("v-w", out (v - w), exact), ("2v", out (two * v), exact),
   ("v*2", out (v * two), exact), ("v/2", out (v / two), exact), ("-v", out (-v), exact),
   ("v∧w", out (v ∧ w), prods), ("v∨w", out (v ∨ w), prods), ("v*w", out (v * w), prods),
   ("v⋅w", out (v ⋅ w), prods), ("v×w", out (v × w), prods), ("⋆v", out (⋆v), prods),
   ("!v", out (complementRight v), prods), ("~(v*w)", out (~(v * w)), prods),
   ("a*v", out (a * v), exact), ("v*a", out (v * a), exact), ("v/b", out (v / b), exact),
   ("norm(v)", out v.norm, exact), ("abs(v)", out v.abs, exact), ("abs2(v)", out v.abs2Chain, exact),
   ("inv(v)", out (v⁻¹), exact), ("unit(v)", out v.unit, exact), ("scalar(q)", out (scalar q), prods),
   ("bivector(q)", out (bivector q), prods), ("v<w", out (v.lt w), prods), ("q*q", out (q * q), prods),
   ("q+q", out (q + q), prods), ("v*q", out (v * q), prods), ("q*v", out (q * v), prods),
   ("v∧w∧v", out ((v ∧ w) ∧ v), prods), ("⋆(v∧w)", out (⋆(v ∧ w)), prods),
   ("(v∧w)⋅v", out ((v ∧ w) ⋅ v), prods), ("v⊘q", out (v ⊘ q), prods),
   ("clifford(q)", out (clifford q), prods), ("v+q", out (v + q), prods)]

/-- Run the 2-D field algebra checks. -/
def run : TestM Unit := do
  let j ← load "field2d"
  let o ← jField j "ops"
  for (name, got, tol) in ops do
    checkField s!"field2d {name}" got (← jField o name) tol
  checkFloat "field2d sum(a)" a.sumF (← jField o "sum(a)")
  checkFloat "field2d prod(b)" b.prodF (← jField o "prod(b)")
  checkFloat "field2d supnorm(v)" v.supnorm (← jField o "supnorm(v)")
  checkFloat "field2d infnorm(v)" v.infnorm (← jField o "infnorm(v)")
  checkFloats "field2d sum(v)" (flatOf [v.sum]) (← gFloats (← jField o "sum(v)"))
  let fr : LocalTensor (Coordinate (AffinePoint 2)) Float := (a - (1.1 : Float)).findroot
  let jf ← jField o "findroot(a-1.1)"
  checkFloats "field2d findroot base" (flatOf [fr.base.point]) (← gFloats (← jField jf "base"))
  checkFloat "field2d findroot fiber" fr.fiber (← jField jf "fiber")
  let mx : LocalTensor (Coordinate (AffinePoint 2)) Float := a.maximum
  let jm ← jField o "maximum(a)"
  checkFloats "field2d maximum base" (flatOf [mx.base.point]) (← gFloats (← jField jm "base"))
  checkFloat "field2d maximum fiber" mx.fiber (← jField jm "fiber")
  let js ← jArr (← jField o "split(v)")
  let comps := v.split
  check "field2d split(v) count" (comps.size == js.size)
  for (c, jc) in comps.toList.zip js.toList do
    checkFloats "field2d split(v)" c.data (← gFloats jc)

end Tests.CartanTests.Field2d
