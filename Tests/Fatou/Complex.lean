import Tests.Fatou.Harness

/-!
`ComplexF64` primitives against `oracle/golden/fatou/complex.json` (port-notes/fatou.md G4):
~750 operand pairs (random magnitudes over 40 decades, signed zeros, subnormals, `Inf`,
`NaN`). The IEEE-only operations must agree bit for bit; the ones that call libm
(`atan2`, `exp`, `sin`, `cosh`, `log`, …) within a few ulps, since Julia uses its own
implementations of those.
-/

namespace Tests.Fatou.Complex

open _root_.Fatou Tests.Fatou

/-- Ulp budget for libm-based results (Julia's own `sin`/`exp`/`atan` vs the platform's). -/
def libmUlps : Nat := 4

/-- Run the suite. -/
def run : TestM Unit := do
  let j ← readJson "complex.json"
  let cases ← gArr j "cases"
  let mut libmWorst : Nat := 0
  for c in cases do
    let z ← gC c "z"
    let w ← gC c "w"
    let x ← gF c "x"
    let lbl := s!"z={hexOf z.re},{hexOf z.im}"
    let exact (name : String) (got : C64) : TestM Unit := do
      let e ← gC c name
      check s!"{name} {lbl}" (sameC got e) fun _ =>
        s!"got ({got.re}, {got.im}) expected ({e.re}, {e.im})"
    exact "mul" (z * w)
    exact "div" (z / w)
    exact "inv" (C64.inv z)
    exact "add" (z + w)
    exact "sub" (z - w)
    exact "addx" (z + x)
    exact "subx" (z - x)
    exact "xsub" (x - z)
    exact "mulx" (x * z)
    exact "divx" (z / x)
    exact "xdiv" (x / z)
    exact "sqrt" (C64.sqrt z)
    exact "plane" (C64.plane z)
    exact "disk" (C64.disk z)
    let eAbs ← gF c "abs"
    check s!"abs {lbl}" (sameF z.abs eAbs) fun _ => s!"got {z.abs} expected {eAbs}"
    let eAbs2 ← gF c "abs2"
    check s!"abs2 {lbl}" (sameF z.abs2 eAbs2) fun _ => s!"got {z.abs2} expected {eAbs2}"
    let lits ← gArr c "lit"
    let pows ← gArr c "pow"
    for i in [0:lits.size] do
      let k : Int := (i : Int) - 3
      let e ← hexC lits[i]!
      let got := C64.literalPow z k
      check s!"literal z^{k} {lbl}" (sameC got e) fun _ => s!"got ({got.re}, {got.im}) expected ({e.re}, {e.im})"
      let e ← hexC pows[i]!
      let got := C64.powInt z k
      check s!"runtime z^{k} {lbl}" (sameC got e) fun _ => s!"got ({got.re}, {got.im}) expected ({e.re}, {e.im})"
    -- libm tier
    let eAng ← gF c "angle"
    let d := ulps z.angle eAng
    libmWorst := max libmWorst d
    check s!"angle {lbl}" (d ≤ libmUlps) fun _ => s!"got {z.angle} expected {eAng} ({d} ulps)"
    for (name, got) in [("exp", C64.exp z), ("sin", C64.sin z), ("cos", C64.cos z),
        ("sinh", C64.sinh z), ("cosh", C64.cosh z), ("log", C64.log z)] do
      let e ← gC c name
      let d := max (ulps got.re e.re) (ulps got.im e.im)
      if d < 1000000 then libmWorst := max libmWorst d
      -- far from 1 ulp only where the result is dominated by rounding noise of a tiny part
      let ok := d ≤ libmUlps || closeC got e libmUlps (1e-300)
      check s!"{name} {lbl}" ok fun _ => s!"got ({got.re}, {got.im}) expected ({e.re}, {e.im}) ({d} ulps)"
  note s!"complex: {cases.size} operand pairs; worst libm-tier distance {libmWorst} ulps"

end Tests.Fatou.Complex
