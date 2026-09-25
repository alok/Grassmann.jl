import Tests.Similitude.Common

/-!
# Similitude: quantity arithmetic and conversion

Against `oracle/golden/similitude/quantity_arith.json`: random quantities
`U(x, d₁)`, `U(y, d₂)` with Julia values `1, 2, 3, 0.5, 2.5, 1//3`, and the
display of `a`, `b`, `a*b`, `a/b`, `inv(a)`, `a^2`, `sqrt(a)`, `a(Metric)`,
`a(English)`, computed through the typed API with the dimensions supplied at
runtime (the types are still checked: `a * b : Q U (d₁ * d₂)`).

Also compile-time checks of the typed API.
-/

namespace Tests.SimilitudeTests

open Lean Tests.Units FieldConstants FieldAlgebra UnitSystems Similitude

/-! Julia `dimensions`/`Dimension` (`dimension.jl:230, 303-305`). -/
#guard (Sys.Metric.qty Dim.energy (2.0 : Float)).dimensions.print == "FL"
#guard (Dimension (Sys.English.qty Dim.magneticflux (1 : Scalar))).print ==
  (Dim.magneticflux.toGroup).print
#guard (Dim.conv Dim.power .Metric .English).dimensions.print == "FLT⁻¹"

/-! Typed quantities: the dimension is computed by the elaborator. -/
example : Q .Metric (USQ.F * USQ.F * USQ.L) :=
  Sys.Metric.qty Dim.energy (2 : Scalar) * Sys.Metric.qty Dim.force (3 : Scalar)
example : Q .Metric Dim.length := Sys.Metric.qty Dim.energy (2 : Scalar) / Sys.Metric.qty Dim.force (4 : Scalar)
example : Q .English Dim.power := (Sys.Metric.qty Dim.power (1 : Scalar)).to .English
example : Quantity .Metric Dim.area Float := ((Sys.Metric.qty Dim.area 4.0).sqrt).npow 2
-- `action` and `angularmomentum` coincide in Metric (the angle is dimensionless there) …
example : Q .Metric Dim.angularmomentum := (Sys.Metric.qty Dim.action (1 : Scalar)).recast _
-- … but not in MetricDegree, where `recast` does not typecheck:
/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: Tactic `decide` proved that the proposition
  Sys.MetricDegree.hom.halfDim Dim.action = Sys.MetricDegree.hom.halfDim Dim.angularmomentum
is false
-/
#guard_msgs in
example : Q .MetricDegree Dim.angularmomentum := (Sys.MetricDegree.qty Dim.action (1 : Scalar)).recast _

-- Adding an energy to a force, or a Metric length to an English one, is a type error:
example : True := by
  fail_if_success
    have : Q .Metric Dim.energy := Sys.Metric.qty Dim.energy (1 : Scalar) + Sys.Metric.qty Dim.force 1
  fail_if_success
    have : Q .Metric Dim.length := Sys.Metric.qty Dim.length (1 : Scalar) + Sys.English.qty Dim.length 1
  have : Q .Metric Dim.length := Sys.Metric.qty Dim.length (1 : Scalar) + Sys.Metric.qty Dim.length 1
  trivial

/-- Quantity arithmetic and conversions with runtime dimensions. -/
def quantitySuite : IO Suite := do
  let j ← loadJson "similitude/quantity_arith.json"
  let mut s : Suite := { name := "quantity arithmetic" }
  for r in arr j do
    let U := sysOf! (str (idx r 0))
    let (some q1, some q2) := (Conv.ofName? (str (idx r 1)), Conv.ofName? (str (idx r 2)))
      | s := s.check false fun _ => "unknown quantity"
    let a : Q U q1.dim := ⟨scalarOf (idx r 3)⟩
    let b : Q U q2.dim := ⟨scalarOf (idx r 4)⟩
    let tag := s!"{U.name}: {q1.name}, {q2.name}"
    let chk (s : Suite) (k : Nat) (what : String) (got : String) : Suite :=
      s.check (got == str (idx r k)) fun _ => s!"{tag} {what}: got {got}, want {str (idx r k)}"
    s := chk s 5 "a" (toString a)
    s := chk s 6 "b" (toString b)
    s := chk s 7 "a*b" (toString (a * b))
    s := chk s 8 "a/b" (toString (a / b))
    s := chk s 9 "inv" (toString a.inv)
    s := chk s 10 "a^2" (toString (a.npow 2))
    if h : q1.dim.IsSquare then s := chk s 11 "sqrt" (toString (a.sqrt h))
    else s := s.check false fun _ => s!"{tag}: no square root"
    s := chk s 12 "a(Metric)" (toString (a.to .Metric))
    s := chk s 13 "a(English)" (toString (a.to .English))
  return s

end Tests.SimilitudeTests
