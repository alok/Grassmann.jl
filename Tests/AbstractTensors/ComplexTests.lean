/-
Oracle tests for `JuliaBase.ComplexF64` (Julia `Base` on `ComplexF64`) and
the scalar helpers `F64.expm1`, `F64.log1p`, `F64.hypot`.

Pure arithmetic (`*`, `/`, `inv`, `abs = hypot`, `sqrt`), the real `expm1`/`log1p` and the
real part of the complex `log` (Julia's own kernels, `JuliaBase.Math`) must agree bitwise;
functions that call the trigonometric `libm` (Julia uses its own port) are compared to a few
ulps, measured on each component against the magnitude of the result.
-/
import AbstractTensors
import Tests.AbstractTensors.Harness
import Tests.AbstractTensors.Golden

namespace Tests.AbstractTensors.ComplexTests

open _root_.AbstractTensors StaticVectors JuliaBase

/-- The unary `Complex Float` functions under test, by Julia name. -/
def unary : String → Option (Complex Float → Complex Float)
  | "inv" => some ComplexF64.inv
  | "abs" => some fun z => ⟨ComplexF64.abs z, 0⟩
  | "sqrt" => some ComplexF64.sqrt
  | "exp" => some ComplexF64.exp
  | "expm1" => some ComplexF64.expm1
  | "log" => some ComplexF64.log
  | "log1p" => some ComplexF64.log1p
  | "sin" => some ComplexF64.sin
  | "cos" => some ComplexF64.cos
  | "tan" => some ComplexF64.tan
  | "sinh" => some ComplexF64.sinh
  | "cosh" => some ComplexF64.cosh
  | "tanh" => some ComplexF64.tanh
  | "asin" => some ComplexF64.asin
  | "acos" => some ComplexF64.acos
  | "atan" => some ComplexF64.atan
  | "asinh" => some ComplexF64.asinh
  | "acosh" => some ComplexF64.acosh
  | "atanh" => some ComplexF64.atanh
  | _ => none

/-- Functions expected to match Julia bit for bit (no `libm` calls). -/
def exactUnary : List String := ["inv", "abs", "sqrt"]

/-- Component-wise closeness to `k` ulps, or to `k·eps` of the result's
magnitude (a component far below the magnitude has meaningless ulps). -/
def cclose (k : Nat) (got want : Complex Float) : Bool :=
  let scale := F64.max (F64.hypot want.re want.im) (F64.hypot got.re got.im)
  let comp (x y : Float) := ulpClose k x y ||
    (x.isFinite && y.isFinite && (x - y).abs ≤ Float.ofNat k * F64.eps * scale)
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
      -- `log(z)`'s real part is `log1p`/`log` of the modulus only: Julia's kernels, bitwise
      if name == "log" then
        check (same got.re want.re) fun _ => s!"complex log({showC z}).re: got {showF got.re}, want {showF want.re}"
  for (name, are, aim, bre, bim, rre, rim) in Golden.complexBaseBin do
    let a : Complex Float := ⟨fb are, fb aim⟩
    let b : Complex Float := ⟨fb bre, fb bim⟩
    let want : Complex Float := ⟨fb rre, fb rim⟩
    let (got, ok) := match name with
      | "div" => let g := ComplexF64.div a b; (g, same g.re want.re && same g.im want.im)
      | "mul" => let g := a * b; (g, same g.re want.re && same g.im want.im)
      | _ => let g := ComplexF64.pow a b; (g, cclose 16 g want)
    check ok fun _ => s!"complex {name}({showC a}, {showC b}): got {showC got}, want {showC want}"
  for (name, x, r) in Golden.floatBase do
    let got := if name == "expm1" then F64.expm1 (fb x) else F64.log1p (fb x)
    check (same got (fb r)) fun _ =>
      s!"float {name}({showF (fb x)}): got {showF got}, want {showF (fb r)}, ulps {F64.ulpDist got (fb r)}"
  for (x, y, r) in Golden.hypotCases do
    let got := F64.hypot (fb x) (fb y)
    check (same got (fb r)) fun _ => s!"hypot({fb x}, {fb y}): got {showF got}, want {showF (fb r)}"
  -- Julia facts from the port notes (§6.5): `(im)ǂ == -im`, `unit(3+4im) == 0.6+0.8im`.
  let im' : Complex Float := ⟨0, 1⟩
  check (conj im' == (⟨0, -1⟩ : Complex Float)) fun _ => "conj(im)"
  let z34 : Complex Float := ⟨3, 4⟩
  let u := z34 / ComplexF64.abs z34
  check (same u.re 0.6 && same u.im 0.8) fun _ => s!"unit(3+4im) = {showC u}"
  -- Julia mixed real/complex arithmetic keeps the imaginary part untouched.
  let mz : Complex Float := ⟨1, -0.0⟩
  check (same ((1.0 : Float) + mz).im (-0.0)) fun _ => "1.0 + z keeps -0.0im"
  check (same ((2.0 : Float) * mz).im (-0.0)) fun _ => "2.0 * z keeps -0.0im"

end Tests.AbstractTensors.ComplexTests
