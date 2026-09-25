import Tests.Similitude.Common

/-!
# Similitude: homomorphisms and dimension display

Against `oracle/golden/similitude/{homs,unified}.json`: for all 48 systems and
all 131 convertible quantities, the image `U(d)` (exact exponents), its USQ
display, and the display of `U(1, d)` through the unit-name registry; and the
isomorphism `UnitSystem(d)` with its `Unified` display.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Exact equality of exponent vectors including the element type. -/
def expsSame : Exps 11 → Exps 11 → Bool
  | .exact u, .exact v => u == v
  | .float u, .float v => (List.finRange 11).all fun i => sameBits (u.get i) (v.get i)
  | _, _ => false

/-- The USQ group of a named quantity. -/
def convGroup (q : Conv) : USQGroup := q.dim.toGroup

/-- Homomorphism images and displays for every system and quantity. -/
def homsSuite : IO Suite := do
  let j ← loadJson "similitude/homs.json"
  let mut s : Suite := { name := "homomorphisms" }
  for sysRow in arr j do
    let sn := str (idx sysRow 0)
    let U := sysOf! sn
    s := s.check (U.name == str (idx sysRow 1)) fun _ => s!"unitname {sn}: {U.name}"
    for r in arr (idx sysRow 2) do
      let some q := Conv.ofName? (str (idx r 0)) | s := s.check false fun _ => s!"no Conv {str (idx r 0)}"
      let d := (convGroup q).v
      let img := U.image d
      let want := expsOfStr 11 (str (idx r 1))
      s := s.check (expsSame img want) fun _ => s!"{sn}({q.name}) image"
      let imgShow := (Group.mk' img (.int 1) : USQGroup).print
      s := s.check (imgShow == str (idx r 2)) fun _ => s!"{sn}({q.name}): got {imgShow}, want {str (idx r 2)}"
      let qs := s!"1 [{U.showDim d}] {U.name}"
      s := s.check (qs == str (idx r 3)) fun _ => s!"{sn}(1,{q.name}): got {qs}, want {str (idx r 3)}"
  return s

/-- `UnitSystem(d)` and the `Unified` display. -/
def unifiedSuite : IO Suite := do
  let j ← loadJson "similitude/unified.json"
  let mut s : Suite := { name := "UnitSystem(d) / Unified" }
  for r in arr j do
    let some q := Conv.ofName? (str (idx r 0)) | s := s.check false fun _ => s!"no Conv {str (idx r 0)}"
    let d := (convGroup q).v
    s := s.check (expsSame d (expsOfStr 11 (str (idx r 1)))) fun _ => s!"dim {q.name}"
    s := s.check (expsSame (usqMap.apply d) (expsOfStr 11 (str (idx r 2)))) fun _ => s!"UnitSystem({q.name})"
    let qs := s!"1 [{showDimUnified d}] Unified"
    s := s.check (qs == str (idx r 3)) fun _ => s!"Unified(1,{q.name}): got {qs}, want {str (idx r 3)}"
  return s

end Tests.SimilitudeTests
