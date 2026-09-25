import Tests.Forms.Common

/-!
# Floating-point operator algebra against Julia (`oracle/golden/forms/float.json`)

Random and structured real matrices, `n = 1 … 6`. Bit for bit: the Cramer inverse,
`invdet`, `\`, `det`, the characteristic polynomial and `eigpolys`, `scalar`, `T/3`
(Julia divides a tensor by a number through the reciprocal), and `exp`/`expm1` (Grassmann's
Padé scaling and squaring; the `2 × 2` closed form goes through the C library's
`cosh`/`sinh`/`cos`/`sin`, compared to `1e-14`). Eigenvalues: `rtol = 1e-12` for the
closed-form roots (`n < 5`; the Viète branch uses `acos`/`cos`), `1e-9` against LAPACK
(`n ≥ 5`); `sylvester` and `discriminant` follow the eigenvalues. Display strings exactly.
-/

namespace Tests.FormsTests.FloatSuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- One golden case. -/
def check (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let rowsA := floatRows (fld c "A")
  let n := rowsA.length
  let V := En n
  let A : Endomorphism V (.chain 1) Float := endo V rowsA
  let b : Chain V 1 Float := chainOf V 1 (flts (fld c "b"))
  let w := fun (s : String) => fun (_ : Unit) => s!"case {k} (n={n}) {s}"
  let mut t := t
  t := t.num .bits (.flt A.det) (fld c "det") (w "det")
  t := t.mat .bits (opRows A.inv) (fld c "inv") (w "inv")
  t := t.num .bits (.flt A.invdet.2) (fld c "invdet") (w "invdet")
  t := t.nums .bits (vals (A.ldiv b).v) (fld c "solve") (w "T\\b")
  t := t.nums .bits (vals (A.solve b).v) (fld c "cramer") (w "value(T)\\b")
  t := t.nums .bits (vals A.characteristic.v) (fld c "characteristic") (w "characteristic")
  t := t.nums .bits (vals A.eigpolys.v) (fld c "eigpolys") (w "eigpolys")
  t := t.num .bits (.flt A.scalar) (fld c "scalar") (w "scalar")
  t := t.mat .bits (opRows (A / (3 : Float))) (fld c "div3") (w "T/3")
  let er : Mode := if n < 5 then .approx 1e-12 else .approx 1e-9
  if n ≥ 2 then t := t.num (.approx 1e-9) (.flt A.discriminant) (fld c "discriminant") (w "discriminant")
  -- against LAPACK (`n ≥ 5`) the `(re, im)` order can depend on rounding noise
  let uo := n ≥ 5
  t := Tally.spectrum t er A.eigvals (fld c "eigvals") (w "eigvals") uo
  match A.eigvalsreal with
  | .ok v => t := (if n ≥ 5 then Tally.numsSet else Tally.nums) t er (vals v) (fld c "eigvalsreal") (w "eigvalsreal")
  | .error e =>
    t := t.ok ((jerr? (fld c "eigvalsreal")).isSome) (w s!"eigvalsreal: Lean error {e}, Julia {(fld c "eigvalsreal").compress}")
  -- Julia's `eigvalscomplex` of a 1×1 operator is `Complex(X[1])`, the column's coefficient
  -- as the *imaginary* part (`forms.jl:1418`)
  if n ≥ 2 then
    t := (if uo then Tally.numsSet else Tally.nums) t er (vals A.eigvalscomplex) (fld c "eigvalscomplex")
      (w "eigvalscomplex")
  else t := t.skip
  if n ≥ 2 then
    t := Tally.spectrum t (.approx 1e-9) A.sylvester (fld c "sylvester") (w "sylvester") uo
    t := t.nums .bits (vals A.eigmults) (fld c "eigmults") (w "eigmults")
  else
    t := t.skip.skip  -- Julia's `sylvester`/`eigmults` of a 1×1 operator throw (`UndefVarError: T`)
  let em : Mode := if n == 2 then .approx 1e-14 else .bits
  if (jerr? (fld c "exp")).isNone then
    t := t.mat em (opRows A.exp) (fld c "exp") (w "exp")
    t := t.mat em (opRows A.expm1) (fld c "expm1") (w "expm1")
    t := t.mat em (opRows (A / (10 : Float)).exp) (fld c "exp10") (w "exp(T/10)")
  else t := t.skip  -- Julia's 2×2 `exp` hangs when the discriminant vanishes
  t := t.str A.showJulia (fld c "show") (w "show")
  t := t.str A.inv.displayBody (fld c "displayInv") (w "display(inv)")
  t := t.str A.inv.showJulia (fld c "showInv") (w "show(inv)")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "float"
  return (cases j).toList.zipIdx.foldl (fun t (c, k) => check t c k) (Tally.new "forms/float")

end Tests.FormsTests.FloatSuite
