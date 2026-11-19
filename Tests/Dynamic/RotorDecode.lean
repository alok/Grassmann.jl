/- Checked R3 decoding and exact rational rotor actions, with independent coordinates.
Attribution: independent Lean port of Michael Reed/chakravala's Grassmann ecosystem. -/
import Tests.Dynamic.Common
import Grassmann.Kernel.R3RotorLaws

open Grassmann DirectSum StaticVectors
open Grassmann.Kernel

namespace DynamicTests.RotorDecode

private abbrev bogusKernels : Kernels ℝ3 :=
  { bin := fun _ _ _ _ _ _ => Values.ofFn fun _ => AbstractTensors.Coeff.zero }

private abbrev adversarialCoeff : Coeff Int := { (inferInstance : Coeff Int) with
  add := fun a b => 10 * a + b
  sub := fun a b => 10 * a - b
  mul := fun a b => 10 * a + b
  neg := fun p => 100 + p
  zero := 5
  ofRat := fun _ => 7 }

private def sameRaw {V : TensorBundle} (x y : TA V Rat) : Bool :=
  x.kind.name == y.kind.name && x.grade? == y.grade? && x.bits? == y.bits? &&
    x.toDense.v.toList == y.toDense.v.toList && x.showString == y.showString &&
    x.showCompact == y.showCompact

/-- Scalar decoding copies coefficients for every actual Coeff, without algebraic laws. -/
theorem arbitraryScalar {α : Type} [Coeff α] (q : α) :
    R3Rotor.decode (TA.chain 0 (R3Rotor.scalarChain q) : TA ℝ3 α) =
      R3Rotor.decode (.single 0 q) := R3Rotor.decode_scalar q

/-- Every-mask scalar consumers retain the distinction between storage and denotation. -/
theorem arbitraryCoefficient {α : Type} [Coeff α] (q : α) (mask : UInt64) :
    (TA.chain 0 (R3Rotor.scalarChain q) : TA ℝ3 α).coeff mask =
      (TA.single 0 q : TA ℝ3 α).coeff mask := R3Rotor.scalar_coeff q mask

/-- Checked normalization preserves the complete Option-valued denotation. -/
theorem arbitraryNormalization {α : Type} [Coeff α] (x : TA ℝ3 α) :
    (R3Rotor.normalize x).bind R3Rotor.decode = R3Rotor.decode x :=
  R3Rotor.decode_normalize x

/-- Higher-order consumers use the actual generated exact action theorem. -/
theorem exactArgument {β : Type} (x y z : Rat) (f : Chain ℝ3 1 Rat → β) :
    f (R3Rotor.action x y z) = f (R3Rotor.coordinates x y z) :=
  congrArg f (R3Rotor.action_formula x y z)

/-- The decoder is still computational for arbitrary Float values, with no Float laws. -/
theorem floatScalar (q : Float) :
    R3Rotor.decode (TA.chain 0 (R3Rotor.scalarChain q) : TA ℝ3 Float) =
      R3Rotor.decode (.single 0 q) := arbitraryScalar q

/-- Expected TA forward notation selects the dynamic projected method. -/
theorem forwardDispatch (v : Chain ℝ3 1 Rat) :
    ((R3Rotor.rotor >>> (TA.chain 1 v : TA ℝ3 Rat)) : TA ℝ3 Rat) =
      TA.tsandwich (.spinor R3Rotor.rotor) (.chain 1 v) := rfl

/-- Expected TA backward notation has the opposite convention. -/
theorem backwardDispatch (v : Chain ℝ3 1 Rat) :
    (((TA.chain 1 v : TA ℝ3 Rat) ⊘ R3Rotor.rotor) : TA ℝ3 Rat) =
      TA.sandwich (.chain 1 v) (.spinor R3Rotor.rotor) := rfl

example (_x : TA ℝ3 Rat) : True := by
  fail_if_success have : Multivector ℝ3 Rat := R3Rotor.decode _x
  fail_if_success have : LawfulCoeff Float := inferInstance
  fail_if_success have : Lean.Grind.Field Float := inferInstance
  trivial

/-- An independent fixture contains input, forward result, and opposite-convention result. -/
abbrev XYZ := Rat × Rat × Rat

/-- Exact matrix values entered independently of the generated Clifford products. -/
def cases : List (XYZ × XYZ × XYZ) :=
  [((0,0,0),(0,0,0),(0,0,0)),
   ((1,0,0),(-7/25,-24/25,0),(-7/25,24/25,0)),
   ((0,1,0),(24/25,-7/25,0),(-24/25,-7/25,0)),
   ((0,0,1),(0,0,1),(0,0,1)),
   ((1,2,3),(41/25,-38/25,3),(-11/5,2/5,3)),
   ((-2/3,5/7,-3/11),(458/525,11/25,-3/11),(-262/525,-21/25,-3/11)),
   ((24,7,-2),(0,-25,-2),(-336/25,527/25,-2))]

/-- Separate fused-provider replacement; both methods deliberately return their input. -/
@[instance_reducible] def identitySandwich : SandwichKernels ℝ3 where
  sandwich _ _ _ x := x
  tsandwich _ _ _ x := x
  rsandwich _ _ _ _ _ := Values.ofFn fun _ => AbstractTensors.Coeff.zero

/-- Complete grade-one coefficients in actual stored order. -/
def xyz (v : Chain ℝ3 1 Rat) : XYZ :=
  (v.v.get ⟨0, by decide⟩,v.v.get ⟨1, by decide⟩,v.v.get ⟨2, by decide⟩)

/-- Euclidean length is observed on actual output entries. -/
def lengthSq (v : Chain ℝ3 1 Rat) : Rat :=
  let (x,y,z) := xyz v
  x*x+y*y+z*z

/-- Full expected grade-major multivector storage, with every forbidden grade zero. -/
def denseXYZ (x y z : Rat) : List Rat := [0,x,y,z,0,0,0,0]

/-- Compare every mask, including masks outside the R3 space. -/
def coefficients (out : TA ℝ3 Rat) (x y z : Rat) : Bool :=
  ([0,1,2,3,4,5,6,7,8,15] : List UInt64).all fun mask =>
    out.coeff mask == (if mask == 1 then x else if mask == 2 then y
      else if mask == 4 then z else 0)

/-- Compile-time consumer uses the actual local operation-only zero value 5. -/
theorem lawlessScalar :
    letI : Coeff Int := adversarialCoeff
    let a : TA ℝ3 Int := .chain 0 (R3Rotor.scalarChain (7 : Int))
    let b : TA ℝ3 Int := .single 0 7
    a.coeff 0 = 7 ∧ a.coeff 1 = 5 ∧ b.coeff 0 = 7 ∧ b.coeff 1 = 5 := by
  decide +kernel

/-- Decoder admission includes all linear constructors and coincident couple slots. -/
def admitted : List (TA ℝ3 Rat) :=
  [.zero,.one,.blade 0,.blade 7,.single 0 (-2/3),.single 7 (5/7),
   .chain 0 (R3Rotor.scalarChain 0),.chain 1 (R3Rotor.point 1 2 3),
   .spinor R3Rotor.rotor,.cospinor (R3Rotor.fullAction 1 2 3),
   .multi (R3Rotor.point 1 2 3).toMultivector,
   .couple 0 2 3,.couple 3 2 3,.pseudo 7 2 3,.pseudo 3 2 3]

/-- Nonlinear and invalid storage states stay rejected rather than acquiring dense zero. -/
def rejected : List (TA ℝ3 Rat) :=
  [.infinity,.phasor 2 (.single 0 0),.blade 8,.blade 15,.single 8 2,
   .couple 8 2 3,.pseudo 8 2 3]

/-- Representation-level decoding controls do not install ring laws on the Coeff model. -/
def lawlessControls : List (Bool × String) := Id.run do
  let _ : Coeff Int := adversarialCoeff
  let a : TA ℝ3 Int := .chain 0 (R3Rotor.scalarChain (7 : Int))
  let b : TA ℝ3 Int := .single 0 7
  let want : List Int := [7,5,5,5,5,5,5,5]
  return [(a.coeff 0 == 7 && a.coeff 1 == 5 && b.coeff 1 == 5,
      "operation-only coefficients copy actual zero 5"),
    (a.toDense.v.toList == want && b.toDense.v.toList == want,
      "operation-only complete dense storage"),
    ((R3Rotor.decode a).map (fun m => m.v.toList) == some want &&
      (R3Rotor.decode b).map (fun m => m.v.toList) == some want,
      "operation-only scalar decode"),
    ((R3Rotor.normalize a).map (fun m => m.kind.name) == some "Multivector" &&
      (R3Rotor.normalize a).bind R3Rotor.decode == R3Rotor.decode a,
      "operation-only normalization copies complete storage"),
    (a.kind.name == "Chain" && b.kind.name == "Single" &&
      a.bits?.isNone && b.bits? == some 0 &&
      (R3Rotor.decode (TA.zero : TA ℝ3 Int)).map (fun m => m.v.toList) ==
        some [5,5,5,5,5,5,5,5],"operation-only raw constructors and symbolic zero")]

/-- Execute complete exact actions and checked decoding; Float checks are storage only. -/
def run : IO GrassmannTests.Tally := do
  let mut t : GrassmannTests.Tally := {}
  t := t.check ((Layout.chain 1).blades 3 == #[1,2,4] &&
    Layout.even.blades 3 == #[0,3,5,6] && Layout.odd.blades 3 == #[1,2,4,7] &&
    Layout.full.blades 3 == #[0,1,2,4,3,5,6,7]) "rotor-decode: actual layouts"
  t := t.check ((R3Rotor.rotor * R3Rotor.rotor.reverse : Spinor ℝ3 Rat) == Spinor.one &&
    (R3Rotor.rotor.reverse * R3Rotor.rotor : Spinor ℝ3 Rat) == Spinor.one)
    "rotor-decode: actual two-sided unit rotor"
  t := t.check (R3Rotor.rotor.reverse.v.toList == [3/5,-4/5,0,0] &&
    R3Rotor.rotor.clifford == R3Rotor.rotor.reverse)
    "rotor-decode: even reverse and Clifford conjugation"
  for ((x,y,z),forward,backward) in cases do
    let v := R3Rotor.point x y z
    let r : TA ℝ3 Rat := .spinor R3Rotor.rotor
    let vr : TA ℝ3 Rat := .chain 1 v
    for back in [false,true] do
      let (u,w,s) := if back then backward else forward
      let want := R3Rotor.point u w s
      let full : CoSpinor ℝ3 Rat := if back then R3Rotor.rotor.reverse * v * R3Rotor.rotor
        else R3Rotor.fullAction x y z
      let projected := if back then R3Rotor.inverseAction x y z else R3Rotor.action x y z
      let typedPublic : Chain ℝ3 1 Rat := if back then v ⊘ R3Rotor.rotor else R3Rotor.rotor >>> v
      let raw := if back then TA.sandwich vr r else TA.tsandwich r vr
      let syntaxRoute : TA ℝ3 Rat := if back then vr ⊘ r else r >>> vr
      let mixed : TA ℝ3 Rat := if back then vr ⊘ R3Rotor.rotor else R3Rotor.rotor >>> vr
      let named := if back then TA.mul (TA.mul (TA.reverse r) vr) r
        else TA.mul (TA.mul r vr) (TA.reverse r)
      let fast := if back then TA.mulF (TA.mulF (TA.reverseF r) vr) r
        else TA.mulF (TA.mulF r vr) (TA.reverseF r)
      let fastNotation : TA ℝ3 Rat := if back then (~r)*vr*r else r*vr*(~r)
      let reference : Chain ℝ3 1 Rat :=
        if back then ⟨@Kernel.sandwichTwo ℝ3 Rat _ (Kernels.reference ℝ3)
          .even (.chain 1) R3Rotor.rotor.v v.v⟩
        else ⟨@Kernel.tsandwichTwo ℝ3 Rat _ (Kernels.reference ℝ3)
          .even (.chain 1) R3Rotor.rotor.v v.v⟩
      t := t.check (full.v.toList == [u,w,s,0])
        "rotor-decode: all odd slots before projection"
      t := t.check (full.toMultivector.v.toList == denseXYZ u w s &&
        coefficients (.cospinor full) u w s) "rotor-decode: full dense and every mask"
      t := t.check (projected.v.toList == [u,w,s] &&
        projected.toMultivector.v.toList == denseXYZ u w s)
        "rotor-decode: frozen exact projected action"
      t := t.check (typedPublic.v.toList == [u,w,s] && typedPublic == projected)
        "rotor-decode: actual typed public convention"
      t := t.check (sameRaw raw (.chain 1 want))
        "rotor-decode: complete dynamic projected observers"
      t := t.check (sameRaw raw syntaxRoute && sameRaw raw mixed)
        "rotor-decode: notation and expected-TA dispatch"
      t := t.check (named.kind.name == "CoSpinor" && named.bits?.isNone &&
        named.toDense.v.toList == denseXYZ u w s && coefficients named u w s)
        "rotor-decode: unprojected dynamic product and grade leakage"
      t := t.check (sameRaw named fast && sameRaw fast fastNotation)
        "rotor-decode: named fast and notation triple-product routes"
      t := t.check (reference.v.toList == [u,w,s] &&
        reference.toMultivector.v.toList == denseXYZ u w s)
        "rotor-decode: actual two-stage reference interpreter"
      let expectedDense := some (denseXYZ u w s)
      t := t.check ((R3Rotor.decode (.cospinor full)).map (fun m => m.v.toList) == expectedDense &&
        (R3Rotor.decode (.chain 1 projected)).map (fun m => m.v.toList) == expectedDense &&
        (R3Rotor.decode raw).map (fun m => m.v.toList) == expectedDense &&
        (R3Rotor.decode named).map (fun m => m.v.toList) == expectedDense)
        "rotor-decode: complete checked representation bridges"
    let f := R3Rotor.action x y z
    let b := R3Rotor.inverseAction x y z
    t := t.check (lengthSq f == lengthSq v && lengthSq b == lengthSq v)
      "rotor-decode: exact actual-action norm preservation"
    let (a,b,c) := xyz f
    let (d,e,f) := xyz (R3Rotor.inverseAction x y z)
    t := t.check (R3Rotor.inverseAction a b c == v && R3Rotor.action d e f == v)
      "rotor-decode: both actual inverse compositions"
  for x in admitted do
    t := t.check ((R3Rotor.decode x).map (fun m => m.v.toList) == some x.toDense.v.toList)
      "rotor-decode: admitted linear storage copies every dense coefficient"
    t := t.check ((R3Rotor.normalize x).map (fun y => y.kind.name) == some "Multivector" &&
      (R3Rotor.normalize x).bind R3Rotor.decode == R3Rotor.decode x)
      "rotor-decode: explicit dense normalization preserves complete decoding"
  for x in rejected do
    t := t.check ((R3Rotor.decode x).isNone && (R3Rotor.normalize x).isNone)
      "rotor-decode: nonlinear or invalid storage rejected"
    t := t.check (((R3Rotor.normalize x).bind R3Rotor.decode).isNone &&
      ((R3Rotor.decode x).map (fun m => m.v.toList)).isNone)
      "rotor-decode: rejected input propagates None"
  for q in [(-2/3 : Rat),0,1,5/7] do
    let a : TA ℝ3 Rat := .chain 0 (R3Rotor.scalarChain q)
    let b : TA ℝ3 Rat := .single 0 q
    t := t.check (a.kind.name == "Chain" && b.kind.name == "Single" &&
      a.bits?.isNone && b.bits? == some 0 && !sameRaw a b)
      "rotor-decode: scalar raw constructors stay distinct at zero and unit"
    t := t.check (([0,1,2,3,4,5,6,7,8,15] : List UInt64).all (fun mask =>
      a.coeff mask == b.coeff mask && a.coeff mask == (if mask == 0 then q else 0)))
      "rotor-decode: scalar every-mask denotation"
    t := t.check ((R3Rotor.decode a).map (fun m => m.v.toList) == some [q,0,0,0,0,0,0,0] &&
      R3Rotor.decode a == R3Rotor.decode b &&
      (R3Rotor.normalize a).bind R3Rotor.decode == R3Rotor.decode b)
      "rotor-decode: complete scalar decoding and checked normalization"
  for (ok,label) in lawlessControls do t := t.check ok s!"rotor-decode: {label}"
  let negativeZero : TA ℝ3 Float := .single 0 (-0.0)
  t := t.check ((R3Rotor.decode negativeZero).map (fun m =>
    (m.v.get ⟨0, by decide⟩).toBits) == some (-0.0 : Float).toBits)
    "rotor-decode: coefficient copying preserves negative zero bits"
  let nan : TA ℝ3 Float := .single 0 (0.0/0.0)
  t := t.check ((R3Rotor.decode nan).map (fun m =>
    (m.v.get ⟨0, by decide⟩).isNaN) == some true)
    "rotor-decode: representation guard admits stored NaN without numeric-finiteness claim"
  let storedInfinity : TA ℝ3 Float := .single 0 (1.0/0.0)
  t := t.check ((R3Rotor.decode storedInfinity).map (fun m =>
    (m.v.get ⟨0, by decide⟩).toBits) == some (1.0/0.0 : Float).toBits &&
    (R3Rotor.decode (TA.infinity : TA ℝ3 Float)).isNone)
    "rotor-decode: stored Float infinity and symbolic Infinity have distinct guards"
  let frozenProvider := Id.run do
    let _ : Kernels ℝ3 := bogusKernels
    return (R3Rotor.fullAction 1 2 3).v.toList == [41/25,-38/25,3,0] &&
      (R3Rotor.action 1 2 3).v.toList == [41/25,-38/25,3]
  t := t.check frozenProvider "rotor-decode: concrete definitions freeze generated Kernels"
  let sandwichProvider := Id.run do
    let _ : SandwichKernels ℝ3 := identitySandwich
    let replaced : Chain ℝ3 1 Rat := R3Rotor.rotor >>> R3Rotor.point 1 2 3
    return replaced.v.toList == [1,2,3] &&
      (R3Rotor.action 1 2 3).v.toList == [41/25,-38/25,3] &&
      replaced.v.toList != (R3Rotor.action 1 2 3).v.toList
  t := t.check sandwichProvider
    "rotor-decode: fused provider replacement changes ambient but not frozen action"
  return t

end DynamicTests.RotorDecode
