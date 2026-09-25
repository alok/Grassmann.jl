import FieldAlgebra
import Tests.FieldAlgebra.Groups

/-!
# FieldAlgebra `Ring` and bases with values: golden tests

Against `oracle/golden/similitude/ring.json` (`oracle/similitude/ring.jl`):

* the README and documented cases of `@ring xyz x y z`, replayed here with the
  `ring!` command (`x*y^2 ⇒ xy²`, `x+y^2 ⇒ x + y²`, `(x+y)*(x-y) ⇒ x² + y²⋅-1`, …);
* 400 random rings with every operation (ring ± ring, ring ± monomial and
  monomial ± ring, products, powers, scalars, `==`): the terms in Julia's order
  (exponents, coefficient) and the printed form;
* evaluation `f(x…)` of rings whose coefficients are one (Julia drops them);
* a basis with values (`group!` with `(a := 1.5) (b := 2) (c ≡ 2.5) (d := 3)`):
  `product` bit for bit, the ` = value` display and `factorize` of integers and
  floats.
-/

namespace Tests.FieldAlgebra.RingTests

open Lean Tests.Units FieldConstants _root_.FieldAlgebra Tests.FieldAlgebra.GroupTests

ring! xyz x y z
group! Val (a := 1.5) (b := 2) (c ≡ 2.5) (d := 3)

/-- The README cases, by the Julia expression recorded in the golden. -/
def readmeCases : List (String × Ring xyz) :=
  [("x*y^2", x * y ^ 2), ("x*y^2/x", (x * y ^ 2) / x), ("x+y^2", x + y ^ 2),
   ("(x+y)*(x-y)", (x + y) * (x - y)), ("x-x", x - x), ("x+x", x + x), ("x+y+x", x + y + x),
   ("x+y-x", x + y - x), ("(x+y)-(x+y)", (x + y) - (x + y)), ("2x", 2 * x), ("x*2", x * 2),
   ("2.0x", 2.0 * x), ("x/2", x / 2), ("0.5x", 0.5 * x), ("x+1", x + 1), ("1+x", 1 + x),
   ("x-1", x - 1), ("1-x", 1 - x), ("(x+y)^2", (x + y) ^ 2), ("(x+y)^3", (x + y) ^ 3),
   ("inv(x)", x.inv?.getD 0), ("x^-2", (x.zpow? (-2)).getD 0), ("x^0", x ^ 0), ("-x", -x),
   ("-(x+y)", -(x + y)), ("zero", Ring.zero), ("one", 1), ("x+y+z", x + y + z),
   ("(x+y+z)*(x-y)", (x + y + z) * (x - y)), ("(x+2y)*(3x-y)", (x + 2 * y) * (3 * x - y)),
   ("0.5x+0.5y", 0.5 * x + 0.5 * y), ("(x-y)+(y-x)", (x - y) + (y - x)),
   ("(x+y)+(x-y)", (x + y) + (x - y)), ("(x+y)-(x-y)", (x + y) - (x - y)), ("x*y*z", x * y * z),
   ("x/y", x / y), ("x*(y+z)", x * (y + z)), ("(y+z)*x", (y + z) * x), ("2*(x+y)", 2 * (x + y)),
   ("(x+y)*2", (x + y) * 2), ("(x+y)/2", (x + y) / 2), ("x-2x", x - 2 * x), ("2x-x", 2 * x - x),
   ("x-(x+y)", x - (x + y)), ("y-(x+y)", y - (x + y)), ("(x+y)-y", (x + y) - y),
   ("(x+y+z)^2", (x + y + z) ^ 2), ("(x-y)^3", (x - y) ^ 3), ("(2x+3y)^2", (2 * x + 3 * y) ^ 2),
   ("(x*y^-1+z)^2", (x * (y.zpow? (-1)).getD 0 + z) ^ 2)]

/-! Compile-time spot checks (the FieldAlgebra README). -/
#guard (x * y ^ 2).print == "xy²"
#guard (x + y ^ 2).print == "x + y²"
#guard ((x + y) * (x - y)).print == "x² + y²⋅-1"
#guard ((x * y ^ 2) / x).print == "y²"

/-- Decode a ring from its terms. -/
def ringOf (B : Basis) (j : Json) : Ring B :=
  ⟨(arr (fld j "terms")).map fun t => Group.mk' (expsOf B (fld t "v")) (coefOf (fld t "c"))⟩

/-- Compare a Lean ring with its Julia encoding: the same number of terms, each
term's exponents (kind and value) and coefficient (Julia's normalised kind and
value), and the printed form. -/
def ringMatches {B : Basis} [GroupProduct B] (r : Ring B) (j : Json) : Bool × String :=
  let want := ringOf B j
  let okN := r.size == want.size
  let okT := okN && (r.terms.zip want.terms).all fun (g, w) =>
    (List.finRange B.n).all (fun i => expoSame (g.v.get i) (w.v.get i)) && coefSame g.c w.c
  let s := r.print
  let okS := s == str (fld j "show")
  (okT && okS, s!"got {s} ({r.size} terms), want {str (fld j "show")} (terms {okT})")

/-- Run the ring and value-basis goldens. -/
def run : IO Suite := do
  let j ← loadJson "similitude/ring.json"
  let mut s : Suite := { name := "Ring / values" }
  -- README cases
  for r in arr (fld j "readme") do
    let nm := str (idx r 0)
    match readmeCases.lookup nm with
    | none => s := s.check false fun _ => s!"no Lean case for {nm}"
    | some v =>
      let (ok, msg) := ringMatches v (idx r 1)
      s := s.check ok fun _ => s!"{nm}: {msg}"
  -- evaluation (Julia drops coefficients; these rings have coefficients one)
  let evals : List (String × Ring xyz) :=
    [("x+y", x + y), ("x*y^2", x * y ^ 2), ("(x+y)^2", (x + y) ^ 2),
     ("x*y^-1+z", x * (y.zpow? (-1)).getD 0 + z), ("x+y+z", x + y + z)]
  for r in arr (fld j "evals") do
    let nm := str (idx r 0)
    let xs := (arr (idx r 1)).map fun e => (expoOf e).toFloat
    let want := (expoOf (idx r 2)).toFloat
    match evals.lookup nm with
    | none => s := s.check false fun _ => s!"no Lean evaluation case for {nm}"
    | some f =>
      -- Julia's `sum(prod(v.^f.v[i]))` ignores coefficients: compare the terms' sum
      let got := (Ring.mk (f.terms.map fun g => Group.mk' g.v (.int 1))).eval xs
      s := s.check (sameBits got want) fun _ => s!"eval {nm}: got {got}, want {want}"
  -- random rings
  for r in arr (fld j "rings") do
    let a := ringOf xyz (fld r "a")
    let b := ringOf xyz (fld r "b")
    let g := groupOf xyz (fld r "g")
    let n := (int (fld r "n")).toNat
    let k := int (fld r "k")
    s := s.check (a.print == str (fld (fld r "a") "show")) fun _ =>
      s!"decode {str (fld (fld r "a") "show")}: got {a.print}"
    let ops : List (String × Ring xyz) :=
      [("add", a + b), ("sub", a - b), ("mul", a * b), ("addg", a + g), ("gadd", g + a),
       ("subg", a - g), ("gsub", g - a), ("mulg", a * g), ("gmul", g * a), ("divg", a / g),
       ("pow", a ^ n), ("neg", -a), ("kmul", Ring.const (.int k) * a),
       ("divk", a / Ring.const (.int k)), ("addk", a + Ring.const (.int k)),
       ("ksub", Ring.const (.int k) - a)]
    for (nm, v) in ops do
      let w := fld r nm
      if str w != "ERROR" then
        let (ok, msg) := ringMatches v w
        s := s.check ok fun _ => s!"{nm} of {a.print} and {b.print} / {g.print}: {msg}"
    let eq := (fld r "eq").getBool?.toOption.getD false
    s := s.check ((a == b) == eq) fun _ => s!"{a.print} == {b.print}"
    s := s.check (a == a) fun _ => s!"{a.print} == itself"
  -- a basis with values
  for r in arr (fld j "values") do
    let g := groupOf Val (fld r "g")
    let p := GroupValues.product g
    let want := (expoOf (fld r "product")).toFloat
    s := s.check (sameBits p want) fun _ => s!"product {str (fld (fld r "g") "show")}: got {p}"
    s := s.check (g.print == str (fld (fld r "g") "show")) fun _ =>
      s!"display: got {g.print}, want {str (fld (fld r "g") "show")}"
  for r in arr (fld j "factorize") do
    let got : Group Val := match expoOf (idx r 0) with
      | .int n => GroupValues.factorize n
      | e => GroupValues.factorizeF e.toFloat
    let want := groupOf Val (idx r 1)
    let okV := (List.finRange 4).all fun i => expoSame (got.v.get i) (want.v.get i)
    s := s.check (okV && coefSame got.c want.c && got.print == str (fld (idx r 1) "show")) fun _ =>
      s!"factorize {idx r 0}: got {got.print}, want {str (fld (idx r 1) "show")}"
  return s

end Tests.FieldAlgebra.RingTests
