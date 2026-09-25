import Tests.Similitude.Common

/-!
# Similitude: the applied-units accessors

Against `oracle/golden/similitude/accessors.json` (written by
`oracle/similitude/accessors.jl`): `dimensions`, `Dimension`, `quantity` and
`unitsystem2` on a `Quantity` (`dimension.jl:300-307`) and `dimensions`,
`convertDim` on a `ConvertUnit` (`dimension.jl:230-231`).

The two `Quantity` accessors are the interesting half only because Julia stores
the dimension in a runtime field while the Lean port keeps it as a type index:
the golden pins that recovering the group from the index gives Julia's `q.d`
back, for all 14 dimensions × 8 system pairs.

`convertDim` is the one with real content. It drops the base dimensions whose own
`U`-to-`S` ratio is exactly one, so it is *not* `dimensions`; 76 of the 112 rows
differ, and `SI2019 -> CODATA` energy is the partial case (force kept, length
dropped).
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-- Encode an exponent vector the way `oracle/similitude/accessors.jl` does
(`ex`/`ev`): integers bare, rationals `p/q`, `Float64`s as their bit pattern. The
decoder `expsOfStr` in `Common.lean` is the other direction, but it loses the
`Int`-vs-`Rational` eltype distinction, so the goldens are compared as text. -/
def expsToStr {n : Nat} (e : Exps n) : String :=
  " ".intercalate (e.toExpos.toList.map fun
    | .int k => toString k
    | .rat q => if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"
    | .float x => hexOf x)

/-- `dimensions`/`Dimension`/`quantity`/`unitsystem2` and `ConvertUnit`'s
`dimensions`/`convertDim`. -/
def accessorsSuite : IO Suite := do
  let j ← loadJson "similitude/accessors.json"
  let mut s : Suite := { name := "applied-units accessors" }
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    let S := sysOf! (str (idx r 1))
    let nm := str (idx r 2)
    let some cv := Conv.ofName? nm | s := s.check false fun _ => s!"no Conv {nm}"
    let d := cv.dim
    let tag := s!"{nm} {U.name} -> {S.name}"
    let q : Quantity U d Float := ⟨1.0⟩
    let c : ConvertUnit U S d := ⟨⟩
    -- the exponent vector Julia holds in `q.d`, as printed by the goldens
    let expect (k : Nat) := str (idx r k)
    let shown (e : Exps 11) := expsToStr e
    -- 3: the dimension itself; 4,5: dimensions(q) and Dimension(q)
    s := s.check (shown d.toGroup.v == expect 3) fun _ =>
      s!"{tag} dim: got {shown d.toGroup.v}, want {expect 3}"
    s := s.check (shown q.dimensions.v == expect 4) fun _ =>
      s!"{tag} dimensions(q): got {shown q.dimensions.v}, want {expect 4}"
    s := s.check (shown q.Dimension.v == expect 5) fun _ =>
      s!"{tag} Dimension(q): got {shown q.Dimension.v}, want {expect 5}"
    -- Julia asserts `dimensions(q) === Dimension(q)`; here they are the same term
    s := s.check (q.dimensions == q.Dimension) fun _ => s!"{tag}: dimensions ≠ Dimension"
    -- 7: quantity(q) is the value, the same as `normal`
    s := s.check (q.quantity == 1.0 && q.quantity == q.normal) fun _ =>
      s!"{tag} quantity(q): got {q.quantity}"
    -- 8: unitsystem2(q) is the system, by name
    s := s.check (q.unitsystem2.name == expect 8) fun _ =>
      s!"{tag} unitsystem2: got {q.unitsystem2.name}, want {expect 8}"
    s := s.check (q.unitsystem == q.unitsystem2) fun _ => s!"{tag}: unitsystem ≠ unitsystem2"
    -- 9: dimensions(c) keeps every exponent
    s := s.check (shown c.dimensions.v == expect 9) fun _ =>
      s!"{tag} dimensions(c): got {shown c.dimensions.v}, want {expect 9}"
    -- 10: convertDim(c) drops the base dimensions whose ratio is one
    s := s.check (shown c.convertDim == expect 10) fun _ =>
      s!"{tag} convertDim(c): got {shown c.convertDim}, want {expect 10}"
  return s

end Tests.SimilitudeTests
