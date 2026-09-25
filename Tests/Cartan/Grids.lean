import Tests.Cartan.Common

/-!
# Product spaces and parameter domains (`productspace.json`, `parameters.json`)

`ProductSpace`s: size, every point (column-major), the linear index 5, widths, `show` of the
space and of a point. Parameters: every `XParameter` at small sizes (with the B1 shim on the Julia
side): points, fibers, whether the fiber is a lazy range, the topology tables `p`, `r`, `c`, and
the display of the first and last element.
-/

open Lean Tests.Small Cartan JuliaBase Grassmann MeshTopology

namespace Tests.CartanTests.Grids

/-- The product spaces of the goldens. -/
def spaces : List (String × Σ N, ProductSpace N) :=
  [("0:0.1:1", ⟨1, .ofAxes #v[Axis.colon 0 0.1 1]⟩),
   ("0:0.5:2 x 0:1.0:3", ⟨2, .ofAxes #v[Axis.colon 0 0.5 2, Axis.colon 0 1 3]⟩),
   ("LinRange(0,2π,7) x LinRange(-1,1,4)", ⟨2, .ofAxes #v[Axis.linRange 0 twoPiF 7, Axis.linRange (-1) 1 4]⟩),
   ("0:0.25:1 x 1:-0.5:0 x 0:2.0:4",
      ⟨3, .ofAxes #v[Axis.colon 0 0.25 1, Axis.colon 1 (-0.5) 0, Axis.colon 0 2 4]⟩),
   ("0:0.5:1 x 0:1.0:2", ⟨2, .ofAxes #v[Axis.colon 0 0.5 1, Axis.colon 0 1 2]⟩)]

/-- Check the product spaces. -/
def runSpaces : TestM Unit := do
  let j ← load "productspace"
  let cases ← jArr (← jField j "cases")
  for c in cases do
    let name ← jStr (← jField c "name")
    match spaces.lookup name with
    | none => check s!"productspace {name}" false fun _ => "no Lean space"
    | some ⟨_, ps⟩ =>
      let size ← (← jArr (← jField c "size")).mapM jNat
      check s!"productspace {name} size" (ps.size.toList == size.toList)
      checkFloats s!"productspace {name} points" (buildFlat ps.length ps.point) (← gFloats (← jField c "points"))
      checkFloats s!"productspace {name} linear5" (flatOf [ps.point 4]) (← gFloats (← jField c "linear5"))
      checkFloats s!"productspace {name} widths" (flatOf ps.widths.toList) (← gFloats (← jField c "widths"))
      checkStr s!"productspace {name} point5" (toString (ps.point 4)) (← jField c "point5")
      checkStr s!"productspace {name} show" (toString ps) (← jField c "show")

/-- What a parameter golden records. -/
structure ParamOut where
  /-- The field. -/
  field : FieldOut
  /-- Julia `p`, `r`, `c` of the topology. -/
  p : Array Nat
  /-- Julia `r`. -/
  r : Array Nat
  /-- Julia `c`. -/
  c : Array Nat
  /-- `show(tf[1])`, `show(tf[end])`. -/
  first : String
  /-- `show(tf[end])`. -/
  last : String

/-- Summarize a parameter field over a grid. -/
def pout {N : Nat} {P : Type} [GridPoint N P] [FlatFiber P] [ShowFiber P] {b : GridBundle N P}
    (t : TensorField b P) : ParamOut :=
  let (p, _, r) := b.top.toTable
  { field := out t, p, r, c := b.top.collapse.toArray.map (if · then 1 else 0)
    first := toString (t.localAt 0), last := toString (t.localAt (card b - 1)) }

/-- The Lean parameter for a golden case. -/
def param (name : String) (n : List Nat) : Option ParamOut :=
  match name, n with
  | "Open", [a] => some (pout (Parameter.open1 a))
  | "Open", [a, b] => some (pout (Parameter.open #v[a, b]))
  | "Open", [a, b, c] => some (pout (Parameter.open #v[a, b, c]))
  | "Torus", [a] => some (pout (Parameter.torus1 a))
  | "Torus", [a, b] => some (pout (Parameter.torus #v[a, b]))
  | "Torus", [a, b, c] => some (pout (Parameter.torus #v[a, b, c]))
  | "Mirror", [a] => some (pout (Parameter.mirror1 a))
  | "Mirror", [a, b] => some (pout (Parameter.mirror #v[a, b]))
  | "Clamped", [a] => some (pout (Parameter.clamped1 a))
  | "Clamped", [a, b] => some (pout (Parameter.clamped #v[a, b]))
  | "Sphere", [a] => some (pout (Parameter.sphere1 a))
  | "Sphere", [a, b] => some (pout (Parameter.sphere #v[a, b]))
  | "Sphere", [a, b, c] => some (pout (Parameter.sphere #v[a, b, c]))
  | "Ball", [a] => some (pout (Parameter.ball1 a))
  | "Ball", [a, b] => some (pout (Parameter.ball #v[a, b]))
  | "Ball", [a, b, c] => some (pout (Parameter.ball #v[a, b, c]))
  | "Cylinder", [a, b] => some (pout (Parameter.cylinder a b))
  | "Mobius", [a, b] => some (pout (Parameter.mobius a b))
  | "Wing", [a, b] => some (pout (Parameter.wing a b))
  | "Klein", [a, b] => some (pout (Parameter.klein a b))
  | "Cone", [a, b] => some (pout (Parameter.cone a b))
  | "Tube", [a, b] => some (pout (Parameter.tube a b))
  | "Tube", [a, b, c] => some (pout (Parameter.tube3 #v[a, b, c]))
  | "Geographic", [a, b] => some (pout (Parameter.geographic a b))
  | "Hopf", [a, b, c] => some (pout (Parameter.hopf3 #v[a, b, c]))
  | _, _ => none

/-- Check the parameter domains. -/
def runParams : TestM Unit := do
  let j ← load "parameters"
  let cases ← jArr (← jField j "cases")
  for c in cases do
    let name ← jStr (← jField c "param")
    let n ← (← jArr (← jField c "n")).mapM jNat
    let label := s!"parameters {name}{n}"
    if (c.getObjVal? "error").isOk then continue
    match param name n.toList with
    | none => check label false fun _ => "no Lean parameter"
    | some o =>
      let size ← (← jArr (← jField c "size")).mapM jNat
      check s!"{label} size" (o.field.size == size.toList)
      checkFloats s!"{label} points" o.field.points (← gFloats (← jField c "points"))
      checkFloats s!"{label} fiber" o.field.fiber (← gFloats (← jField c "fiber"))
      let fr ← jBool (← jField c "fiberrange")
      check s!"{label} fiberrange" (o.field.isrange == fr) fun _ => s!"got {o.field.isrange}"
      let p ← (← jArr (← jField c "p")).mapM jNat
      let r ← (← jArr (← jField c "r")).mapM jNat
      let cc ← (← jArr (← jField c "c")).mapM jNat
      check s!"{label} p" (o.p == p) fun _ => s!"got {o.p}, expected {p}"
      check s!"{label} r" (o.r == r) fun _ => s!"got {o.r}, expected {r}"
      check s!"{label} c" (o.c == cc) fun _ => s!"got {o.c}, expected {cc}"
      checkStr s!"{label} elem1" o.first (← jField c "elem1")
      checkStr s!"{label} elemlast" o.last (← jField c "elemlast")

/-- Run the grid checks. -/
def run : TestM Unit := do
  runSpaces
  runParams

end Tests.CartanTests.Grids
