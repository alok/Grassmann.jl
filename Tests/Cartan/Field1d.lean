import Tests.Cartan.Common

/-!
# 1-D and complex fields, reductions (`oracle/golden/cartan/field1d.json`)

Julia:

```julia
t = TensorField(0:0.25:2)
z = TensorField(0:0.25:2, x -> Complex(x, 1-x));  z2 = TensorField(0:0.25:2, x -> Complex(1+x, x/2))
big = TensorField(0:0.01:20, x -> x*x/7 - x/3)       # 2001 points: pairwise sums beyond 1024
mid = TensorField(0:0.37:13, x -> x*x/7 - x/3)       # 36 points: the vectorized block
vbig = (x -> Chain(x[1], x[2]*x[1], 1.0+x[2])).(TensorField(ProductSpace(0:0.25:1, 0:0.25:1)))
```
-/

open Lean Tests.Small Cartan JuliaBase Grassmann

namespace Tests.CartanTests.Field1d

/-- `0:0.25:2`. -/
def ax : Axis := Axis.colon 0 0.25 2
/-- Julia `t = TensorField(0:0.25:2)`. -/
def t : TensorField (GridBundle.ofAxis ax) Float := TensorField.ofAxis ax
/-- Julia `z = TensorField(0:0.25:2, x -> Complex(x, 1-x))`. -/
def z : TensorField (GridBundle.ofAxis ax) (Complex Float) := TensorField.ofAxisFn ax fun x => ⟨x, 1 - x⟩
/-- Julia `z2 = TensorField(0:0.25:2, x -> Complex(1+x, x/2))`. -/
def z2 : TensorField (GridBundle.ofAxis ax) (Complex Float) := TensorField.ofAxisFn ax fun x => ⟨1 + x, x / 2⟩
/-- Julia `Chain.(t, t*t)`. -/
def c : TensorField (GridBundle.ofAxis ax) (Chain ℝ2 1 Float) :=
  TensorField.chainOf ℝ2 1 fun j => if j.1 = 0 then t else t * t

/-- The golden operations. -/
def ops : List (String × FieldOut × Tol) :=
  let one : Float := 1
  let two : Float := 2
  [("t", out t, exact), ("sin(t)", out t.sin, libm), ("t^2", out (t.powInt 2), exact),
   ("t^0.5", out (t.pow 0.5), exact), ("sqrt(t)", out t.sqrt, exact), ("exp(t)", out t.exp, exact),
   ("log(t+1)", out (t + one).log, exact), ("t/(t+1)", out (t / (t + one)), exact),
   ("cumsum(t)", out t.cumsum, exact), ("cumprod(t+1)", out (t + one).cumprod, exact),
   ("z", out z, exact), ("z*z", out (z * z), exact), ("z+z2", out (z + z2), exact),
   ("z/z2", out (z / z2), exact), ("exp(z)", out z.exp, libm), ("abs(z)", out z.abs, exact),
   ("conj(z)", out z.conj, exact), ("sqrt(z)", out z.sqrt, exact), ("log(z2)", out z2.log, libm),
   ("2z", out (two * z), exact), ("z*t", out (z * t), exact), ("t*z", out (t * z), exact),
   ("real(z)", out z.re, exact), ("imag(z)", out z.im, exact), ("Chain.(t,t*t)", out c, exact),
   ("norm(Chain.(t,t*t))", out c.norm, exact)]

/-- `0:0.01:20`. -/
def bigAx : Axis := Axis.colon 0 0.01 20
/-- `0:0.37:13`. -/
def midAx : Axis := Axis.colon 0 0.37 13
/-- Julia `x*x/7 - x/3`. -/
def poly (x : Float) : Float := x * x / 7 - x / 3

/-- The 5×5 grid of `vbig`. -/
def g5 : GridBundle 2 (AffinePoint 2) := .ofSpace (.ofAxes #v[Axis.colon 0 0.25 1, Axis.colon 0 0.25 1])
/-- Julia `vbig`. -/
def vbig : TensorField g5 (Chain ℝ3 1 Float) :=
  TensorField.tabulatePoint g5 fun x =>
    Chain.ofFn fun i => #[x.get! 0, x.get! 1 * x.get! 0, 1 + x.get! 1][i.1]!

/-- Run the 1-D field checks. -/
def run : TestM Unit := do
  let j ← load "field1d"
  let o ← jField j "ops"
  for (name, got, tol) in ops do
    checkField s!"field1d {name}" got (← jField o name) tol
  let fr : LocalTensor (Coordinate Float) Float := t.findrootAt 1.1
  let jf ← jField o "findroot(t-1.1)"
  checkFloat "field1d findroot base" fr.base.point (← jField jf "base")
  checkFloat "field1d findroot fiber" fr.fiber (← jField jf "fiber")
  checkFloat "field1d sum(t)" t.sumF (← jField o "sum(t)")
  checkFloat "field1d prod(t+1)" (t + (1 : Float)).prodF (← jField o "prod(t+1)")
  let big := TensorField.ofAxisFn bigAx poly
  checkFloat "field1d sum(big)" big.sumF (← jField o "sum(big)")
  checkFloat "field1d prod(1+big/100)" ((1 : Float) + big / (100 : Float)).prodF (← jField o "prod(1+big/100)")
  let mid := TensorField.ofAxisFn midAx poly
  checkField "field1d mid" (out mid) (← jField o "mid")
  checkFloat "field1d sum(mid)" mid.sumF (← jField o "sum(mid)")
  checkFloat "field1d prod(1+mid/10)" ((1 : Float) + mid / (10 : Float)).prodF (← jField o "prod(1+mid/10)")
  checkField "field1d vbig" (out vbig) (← jField o "vbig")
  checkFloats "field1d sum(vbig)" (flatOf [vbig.sum]) (← gFloats (← jField o "sum(vbig)"))

end Tests.CartanTests.Field1d
