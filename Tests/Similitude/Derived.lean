import Tests.Similitude.Common

/-!
# Similitude: derived units

Against `oracle/golden/similitude/derived.json`: each of Similitude's derived
units (`derived.jl:161-414`) in its own system, converted to `Metric`, its
`Metric` value (bit for bit), its system and its dimension. The functions of the
system (`loschmidt`, `mechanicalheat`) are compared at `Metric`.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Units Similitude does not define as typed quantities (see `Similitude.Units`). -/
def derivedSkipped : List String := ["neper", "bel", "decibel", "rem"]

/-- Derived units against the oracle. -/
def derivedSuite : IO Suite := do
  let j ← loadJson "similitude/derived.json"
  let mut s : Suite := { name := "derived units" }
  for r in arr j do
    let nm := str (idx r 0)
    if derivedSkipped.contains nm then continue
    match Units.table.lookup nm with
    | none => s := s.check false fun _ => s!"no Lean unit {nm}"
    | some ⟨U, d, q⟩ =>
      let isFun := (str (idx r 1)).startsWith "Similitude."
      if !isFun then
        s := s.check (toString q == str (idx r 1)) fun _ => s!"{nm}: got {q}, want {str (idx r 1)}"
        s := s.check (U.name == str (idx r 4)) fun _ => s!"{nm}: system {U.name}, want {str (idx r 4)}"
        s := s.check (ratsOfStr (str (idx r 5)) == d.toRats) fun _ => s!"{nm}: dims {d}"
      let m := q.to .Metric
      s := s.check (toString m == str (idx r 2)) fun _ => s!"{nm}(Metric): got {m}, want {str (idx r 2)}"
      if let some f := goldFloat? (idx r 3) then
        s := s.check (sameBits m.val.toFloat f) fun _ => s!"{nm}(Metric): {hexOf m.val.toFloat} want {hexOf f}"
  return s

end Tests.SimilitudeTests
