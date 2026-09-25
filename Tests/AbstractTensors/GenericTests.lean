/-
Oracle tests for `AbstractTensors.Generic` on scalar carriers.

The Julia oracle (`oracle/gen_goldens.jl`) evaluates the real AbstractTensors
formulas and Grassmann's generic series loops on a scalar "tensor" type whose
value is a `Float64` with unit pseudoscalar `I = 1` (so `I² = +1`: AT's `cos`
is then `cosh`, bug B2) or a `ComplexF64` with `I = im` (`I² = -1`). The two
`TensorRing` instances below mirror that carrier operation for operation, so
every result is expected to agree **bitwise**: the algorithms use only
`+ - * /`, `sqrt`-free arithmetic, `hypot`, Julia's complex `inv`, and (for
`rpow2`/`logb2`) one correctly rounded `log(2.0)`.
-/
import AbstractTensors
import Tests.AbstractTensors.Harness
import Tests.AbstractTensors.Golden

namespace Tests.AbstractTensors.GenericTests

open _root_.AbstractTensors StaticVectors

/-! ### The real carrier: `Float`, `I = 1` -/

instance : SeriesRing Float where
  addScalar k x := k + x
  smul k x := k * x
  sdiv x k := x / k
  norm := Float.abs
  inv x := 1 / x

/-- Julia's scalar carrier `Sc{PS{1.0}(),Float64}`. -/
instance realRing : TensorRing Float :=
  TensorRing.ofSeries 0 1 1 id (fun _ => false) id (· * 1) (· * 1) Float.sqrt Float.cbrt

/-! ### The complex carrier: `Complex Float`, `I = i` -/

instance : SeriesRing (Complex Float) where
  addScalar k z := k + z
  smul k z := k * z
  sdiv z k := z / k
  norm := Complex.abs
  inv := Complex.inv

/-- The imaginary unit, the carrier's pseudoscalar (Julia `float(im) * true`). -/
def iC : Complex Float := ⟨0, 1⟩

/-- Julia's scalar carrier `Sc{PS{im}(),ComplexF64}`. -/
instance complexRing : TensorRing (Complex Float) :=
  TensorRing.ofSeries ⟨0, 0⟩ ⟨1, 0⟩ iC conj (fun _ => false) id (· * iC) (· * iC)
    Complex.sqrt Complex.cbrt

/-- The unary operations under test, by the oracle's names. -/
def unary {X : Type} [TensorRing X] : String → Option (X → X)
  | "expm1" => some TensorRing.expm1
  | "exp" => some TensorRing.exp
  | "cosh" => some TensorRing.cosh
  | "sinh" => some TensorRing.sinh
  | "log" => some TensorRing.log
  | "log1p" => some TensorRing.log1p
  | "sqrt" => some TensorRing.sqrt
  | "cbrt" => some TensorRing.cbrt
  | "qlog" => some (Generic.qlog ·)
  | "cos" => some Generic.cos
  | "sin" => some Generic.sin
  | "tan" => some Generic.tan
  | "cot" => some Generic.cot
  | "sec" => some Generic.sec
  | "csc" => some Generic.csc
  | "tanh" => some Generic.tanh
  | "coth" => some Generic.coth
  | "sech" => some Generic.sech
  | "csch" => some Generic.csch
  | "asinh" => some Generic.asinh
  | "acosh" => some Generic.acosh
  | "atanh" => some Generic.atanh
  | "acoth" => some Generic.acoth
  | "asin" => some Generic.asin
  | "acos" => some Generic.acos
  | "atan" => some Generic.atan
  | "acot" => some Generic.acot
  | "asec" => some Generic.asec
  | "acsc" => some Generic.acsc
  | "asech" => some Generic.asech
  | "acsch" => some Generic.acsch
  | "sinc" => some Generic.sinc
  | "cosc" => some Generic.cosc
  | "exp2" => some Generic.exp2
  | "exp10" => some Generic.exp10
  | "log2" => some Generic.log2
  | "log10" => some Generic.log10
  | "rpow2" => some (Generic.rpow 2)
  | "logb2" => some (Generic.logBase 2)
  | "abs" => some Generic.abs
  | "abs2" => some Generic.abs2
  | "unit" => some Generic.unit
  | "coabs" => some Generic.coabs
  | "geomabs" => some Generic.geomabs
  | "unitnorm" => some Generic.unitnorm
  | "coabs2" => some Generic.coabs2
  | "cosqrt" => some Generic.cosqrt
  | "cocbrt" => some Generic.cocbrt
  | "coexp" => some Generic.coexp
  | "colog" => some Generic.colog
  | "coinv" => some Generic.coinv
  | "cosin" => some Generic.cosin
  | "cocos" => some Generic.cocos
  | "cotan" => some Generic.cotan
  | "cosinh" => some Generic.cosinh
  | "cocosh" => some Generic.cocosh
  | "cotanh" => some Generic.cotanh
  | _ => none

/-- The binary operations under test. -/
def binary {X : Type} [TensorRing X] : String → Option (X → X → X)
  | "div" => some Generic.div
  | "ldiv" => some Generic.ldiv
  | "metric" => some Generic.metric
  | "cometric" => some Generic.cometric
  | _ => none

/-- Render a complex value for failure messages. -/
def showC (z : Complex Float) : String := s!"{showF z.re} + {showF z.im}im"

/-- Run every generic golden. -/
def suite : TestM Unit := do
  for (name, x, r) in Golden.genericReal do
    match unary (X := Float) name with
    | none => check false fun _ => s!"generic real: unknown function {name}"
    | some f =>
      let got := f (fb x)
      check (same got (fb r)) fun _ =>
        s!"generic real {name}({fb x}): got {showF got}, want {showF (fb r)}, ulps {JuliaBase.F64.ulpDist got (fb r)}"
  for (name, re, im, rre, rim) in Golden.genericComplex do
    match unary (X := Complex Float) name with
    | none => check false fun _ => s!"generic complex: unknown function {name}"
    | some f =>
      let got := f ⟨fb re, fb im⟩
      check (same got.re (fb rre) && same got.im (fb rim)) fun _ =>
        s!"generic complex {name}({fb re} + {fb im}im): got {showC got}, want {showC ⟨fb rre, fb rim⟩}"
  for (name, a, b, r) in Golden.genericRealBin do
    match binary (X := Float) name with
    | none => check false fun _ => s!"generic real: unknown binary {name}"
    | some f =>
      let got := f (fb a) (fb b)
      check (same got (fb r)) fun _ =>
        s!"generic real {name}({fb a}, {fb b}): got {showF got}, want {showF (fb r)}"
  for (name, are, aim, bre, bim, rre, rim) in Golden.genericComplexBin do
    match binary (X := Complex Float) name with
    | none => check false fun _ => s!"generic complex: unknown binary {name}"
    | some f =>
      let got := f ⟨fb are, fb aim⟩ ⟨fb bre, fb bim⟩
      check (same got.re (fb rre) && same got.im (fb rim)) fun _ =>
        s!"generic complex {name}: got {showC got}, want {showC ⟨fb rre, fb rim⟩}"
  -- B2 (port-notes §4.2): `cos` of a scalar is `cosh` when `I² = +1` and `cos` when `I² = -1`.
  check (same (Generic.cos (1.0 : Float)) 1.543080634803725) fun _ =>
    s!"B2 cos(1) on I²=+1: {Generic.cos (1.0 : Float)}"
  check (same (Generic.cos (⟨1.0, 0⟩ : Complex Float)).re 0.5403023058795628) fun _ =>
    s!"B2 cos(1) on I²=-1: {(Generic.cos (⟨1.0, 0⟩ : Complex Float)).re}"
  check (same (Generic.sin (⟨1.0, 0⟩ : Complex Float)).re 0.8414709848086585) fun _ =>
    s!"B2 sin(1) on I²=-1: {(Generic.sin (⟨1.0, 0⟩ : Complex Float)).re}"
  -- `exp t = 1 + expm1 t` (AT:329) and the fixed B1: `log(b, t) = log t / log b`.
  check (same (TensorRing.exp (0.5 : Float)) (1 + TensorRing.expm1 (0.5 : Float))) fun _ => "exp = 1 + expm1"
  -- B1 fixed: `log(b, t) = log(t)/log(b)` (Julia returns `log(b)`); the series `log`
  -- stops at a relative change below `√eps`, so it is accurate to about 1e-8.
  check ((Generic.logBase 2 (8.0 : Float) - 3).abs < 1e-7) fun _ =>
    s!"logBase 2 8 = {showF (Generic.logBase 2 (8.0 : Float))}"
  -- Julia `isapprox` on tensors (AT:229), port-notes §6.6 grid: `a ≈ a + 1e-9` holds,
  -- `a ≈ a + 1e-7` fails, `rtol = 1e-6` accepts it, `atol = 1e-2` accepts `a + 1e-3`.
  let za : Complex Float := ⟨1, 2⟩
  let bump (e : Float) : Complex Float := za + (⟨e, 0⟩ : Complex Float)
  check (Generic.isapprox za (bump 1e-9) && !Generic.isapprox za (bump 1e-7) &&
      Generic.isapprox za (bump 1e-7) (rtol := 1e-6) && Generic.isapprox za (bump 1e-3) (atol := 1e-2))
    fun _ => "Generic.isapprox tolerance grid"
  check (Generic.isapprox (⟨Float.nan, 0⟩ : Complex Float) ⟨Float.nan, 0⟩ (nans := true) &&
      !Generic.isapprox (⟨Float.nan, 0⟩ : Complex Float) ⟨Float.nan, 0⟩) fun _ => "isapprox nans"
  check (Generic.isZero (0 : Float) && Generic.isZero (-0.0 : Float) && !Generic.isZero (1e-300 : Float))
    fun _ => "iszero is exact (iszero(1e-300v1) == false)"
  -- A non-finite input terminates (Julia's uncapped loop spins forever on expm1(-Inf)).
  check (TensorRing.expm1 (-Float.inf : Float)).isNaN fun _ => "expm1(-Inf) terminates with NaN"

end Tests.AbstractTensors.GenericTests
