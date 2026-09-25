/-
Oracle tests for `AbstractTensors.Complex` (Julia `Base` on `ComplexF64`) and
the scalar helpers `expm1`, `log1p`, `hypot`.

Pure arithmetic (`*`, `/`, `inv`, `abs = hypot`, `sqrt`) must agree bitwise;
functions that call `libm` (Julia uses its own) are compared to a few ulps,
measured on each component against the magnitude of the result.
-/
import AbstractTensors
import Tests.AbstractTensors.Harness
import Tests.AbstractTensors.Golden

namespace Tests.AbstractTensors.ComplexTests

open _root_.AbstractTensors StaticVectors

/-- The unary `Complex Float` functions under test, by Julia name. -/
def unary : String → Option (Complex Float → Complex Float)
  | "inv" => some Complex.inv
  | "abs" => some fun z => ⟨Complex.abs z, 0⟩
  | "sqrt" => some Complex.sqrt
  | "exp" => some Complex.exp
  | "expm1" => some Complex.expm1
  | "log" => some Complex.log
  | "log1p" => some Complex.log1p
  | "sin" => some Complex.sin
  | "cos" => some Complex.cos
  | "tan" => some Complex.tan
  | "sinh" => some Complex.sinh
  | "cosh" => some Complex.cosh
  | "tanh" => some Complex.tanh
  | "asin" => some Complex.asin
  | "acos" => some Complex.acos
  | "atan" => some Complex.atan
  | "asinh" => some Complex.asinh
  | "acosh" => some Complex.acosh
  | "atanh" => some Complex.atanh
  | _ => none

/-- Functions expected to match Julia bit for bit (no `libm` calls). -/
def exactUnary : List String := ["inv", "abs", "sqrt"]

/-- Component-wise closeness to `k` ulps, or to `k·eps` of the result's
magnitude (a component far below the magnitude has meaningless ulps). -/
def cclose (k : Nat) (got want : Complex Float) : Bool :=
  let scale := Julia.max (Julia.hypot want.re want.im) (Julia.hypot got.re got.im)
  let comp (x y : Float) := ulpClose k x y ||
    (x.isFinite && y.isFinite && (x - y).abs ≤ Float.ofNat k * Julia.epsF * scale)
  comp got.re want.re && comp got.im want.im

/-- Render a complex value for failure messages. -/
def showC (z : Complex Float) : String := s!"{showF z.re} + {showF z.im}im"

/-- Run the complex and float goldens. -/
def suite : TestM Unit := do
  for (name, re, im, rre, rim) in Golden.complexBase do
    match unary name with
    | none => check false fun _ => s!"complex: unknown function {name}"
    | some f =>
      let z : Complex Float := ⟨fb re, fb im⟩
      let got := f z
      let want : Complex Float := ⟨fb rre, fb rim⟩
      let ok := if exactUnary.contains name then same got.re want.re && same got.im want.im
        else cclose 8 got want
      check ok fun _ => s!"complex {name}({showC z}): got {showC got}, want {showC want}"
  for (name, are, aim, bre, bim, rre, rim) in Golden.complexBaseBin do
    let a : Complex Float := ⟨fb are, fb aim⟩
    let b : Complex Float := ⟨fb bre, fb bim⟩
    let want : Complex Float := ⟨fb rre, fb rim⟩
    let (got, ok) := match name with
      | "div" => let g := Complex.div a b; (g, same g.re want.re && same g.im want.im)
      | "mul" => let g := a * b; (g, same g.re want.re && same g.im want.im)
      | _ => let g := Complex.pow a b; (g, cclose 16 g want)
    check ok fun _ => s!"complex {name}({showC a}, {showC b}): got {showC got}, want {showC want}"
  for (name, x, r) in Golden.floatBase do
    let got := if name == "expm1" then FloatExt.expm1 (fb x) else FloatExt.log1p (fb x)
    check (ulpClose 2 got (fb r)) fun _ =>
      s!"float {name}({showF (fb x)}): got {showF got}, want {showF (fb r)}, ulps {Julia.ulpDist got (fb r)}"
  for (x, y, r) in Golden.hypotCases do
    let got := Julia.hypot (fb x) (fb y)
    check (same got (fb r)) fun _ => s!"hypot({fb x}, {fb y}): got {showF got}, want {showF (fb r)}"
  -- Julia facts from the port notes (§6.5): `(im)ǂ == -im`, `unit(3+4im) == 0.6+0.8im`.
  let im' : Complex Float := ⟨0, 1⟩
  check (conj im' == (⟨0, -1⟩ : Complex Float)) fun _ => "conj(im)"
  let z34 : Complex Float := ⟨3, 4⟩
  let u := z34 / Complex.abs z34
  check (same u.re 0.6 && same u.im 0.8) fun _ => s!"unit(3+4im) = {showC u}"
  -- Julia mixed real/complex arithmetic keeps the imaginary part untouched.
  let mz : Complex Float := ⟨1, -0.0⟩
  check (same ((1.0 : Float) + mz).im (-0.0)) fun _ => "1.0 + z keeps -0.0im"
  check (same ((2.0 : Float) * mz).im (-0.0)) fun _ => "2.0 * z keeps -0.0im"

end Tests.AbstractTensors.ComplexTests
