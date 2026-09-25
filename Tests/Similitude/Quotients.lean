import Tests.Similitude.Constants

/-!
# Similitude: quotients `U/~`

Against `oracle/golden/similitude/quotients.json`: the equivalence classes of the
131 convertible quantities under each system's homomorphism, with their keys and
member order.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Quotients of all 48 systems. -/
def quotientSuite : IO Suite := do
  let j ← loadJson "similitude/quotients.json"
  let mut s : Suite := { name := "quotients" }
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    let got := quotient U
    let want := arr (idx r 1)
    s := s.check (got.length == want.size) fun _ => s!"{U.name}: {got.length} classes, want {want.size}"
    for ((k, qs), w) in got.zip want.toList do
      s := s.check (k.print == str (idx w 0)) fun _ => s!"{U.name}: key {k.print}, want {str (idx w 0)}"
      let names := (arr (idx w 1)).toList.map str
      s := s.check (qs.map (·.name) == names) fun _ => s!"{U.name} {k.print}: {qs.map (·.name)}, want {names}"
  return s

/-- `dimlist(U)` and `naturalunits(U)` of all 48 systems. -/
def extrasSuite : IO Suite := do
  let j ← loadJson "similitude/extras.json"
  let mut s : Suite := { name := "dimlist / naturalunits" }
  let bases := [USQ.F, USQ.M, USQ.L, USQ.T, USQ.Q, USQ.Θ, USQ.N, USQ.J, USQ.A, USQ.R, USQ.C]
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    s := s.check (dimlist U == str (idx r 1)) fun _ => s!"dimlist({U.name}): got {dimlist U}, want {str (idx r 1)}"
    for (b, w) in bases.zip (arr (idx r 2)).toList do
      let got := toString (naturalUnit U b)
      s := s.check (got == str w) fun _ => s!"naturalunits({U.name}) {b}: got {got}, want {str w}"
  return s

/-- LaTeX of dimension images (16 systems × 131 quantities) and of named constants. -/
def latexSuite : IO Suite := do
  let j ← loadJson "similitude/latex.json"
  let mut s : Suite := { name := "LaTeX" }
  for r in arr (fld j "dims") do
    let U := sysOf! (str (idx r 0))
    for w in arr (idx r 1) do
      let some q := Conv.ofName? (str (idx w 0)) | s := s.check false fun _ => "unknown quantity"
      let got := U.latexDim q.dim.toGroup.v
      s := s.check (got == str (idx w 1)) fun _ => s!"{U.name} {q.name}: got {got}, want {str (idx w 1)}"
  for r in arr (fld j "constants") do
    let nm := str (idx r 0)
    match namedConstants.lookup nm with
    | some (.grp g) => s := s.check (g.latex == str (idx r 1)) fun _ => s!"{nm}: got {g.latex}, want {str (idx r 1)}"
    | _ => s := s.check false fun _ => s!"no group constant {nm}"
  return s

end Tests.SimilitudeTests
