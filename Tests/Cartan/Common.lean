import Cartan
import Tests.AbstractLattices.Harness

/-!
# Shared helpers for the Cartan golden tests

Goldens live in `oracle/golden/cartan/*.json` (written by `oracle/cartan/gen.jl`). Floats are IEEE
bit patterns `"0x…"`; a field is `{size, fiber, points, isrange, fibertype}` with the fibers and
points flattened point by point (the Lean `FlatFiber` layout); a Julia exception is `{"E": …}`
(these mark Julia defects that the port fixes, and are skipped).

Comparisons are bit-exact, except for results that go through the C `libm` (Lean) versus Julia's
own `openlibm` port (trigonometric and hyperbolic functions): those allow a few ulps
(`F64.ulpDist`).
-/

open Lean Tests.Small Cartan JuliaBase

namespace Tests.CartanTests

/-- Load a Cartan golden file. -/
def load (name : String) : IO Json := readJson s!"oracle/golden/cartan/{name}.json"

/-- Parse `"0x…"` hex bits. -/
def hexBits (s : String) : UInt64 :=
  (s.drop 2).foldl (fun acc c =>
    let d : UInt64 :=
      if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt64
      else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt64
      else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt64 else 0
    acc * 16 + d) 0

/-- A golden float. -/
def gFloat (j : Json) : TestM Float := do return Float.ofBits (hexBits (← jStr j))

/-- A golden float array. -/
def gFloats (j : Json) : TestM FloatArray := do
  let a ← jArr j
  a.foldlM (fun acc x => do return acc.push (← gFloat x)) (FloatArray.emptyWithCapacity a.size)

/-- Julia digits and bits of a float, for messages. -/
def fmt (x : Float) : String := s!"{F64.showString x}"

/-- `true` when the golden value records a Julia exception. -/
def isErr (j : Json) : Bool := (j.getObjVal? "E").isOk

/-- How closely a result must match: `ulps` = 0 is bit-exact (up to the NaN payload); `zeros`
also accepts `0.0` for `-0.0` and back. The Grassmann port's product kernels accumulate from
`+0.0` where Julia's generated code starts from the first product, so products of fibers with
signed zeros can differ in the sign of a zero (`zeros := true` for those). -/
structure Tol where
  /-- Allowed distance in units in the last place. -/
  ulps : Nat := 0
  /-- Accept `±0.0` for each other. -/
  zeros : Bool := false

/-- Bit-exact. -/
def exact : Tol := {}
/-- `libm` results (2 ulps). -/
def libm : Tol := { ulps := 2 }
/-- Grassmann products (signed zeros may differ). -/
def prods : Tol := { zeros := true }

/-- Whether `x` matches `y` within `tol`. -/
def near (tol : Tol) (x y : Float) : Bool :=
  F64.ulpDist x y ≤ tol.ulps || (tol.zeros && x == 0 && y == 0)

/-- Compare two float arrays: equal length, and every pair within `tol`. -/
def checkFloats (label : String) (got want : FloatArray) (tol : Tol := {}) : TestM Unit := do
  if got.size != want.size then
    check label false fun _ => s!"length {got.size}, expected {want.size}"
    return
  let bad := (List.range got.size).find? fun i => !near tol got[i]! want[i]!
  match bad with
  | none => check label true
  | some i => check label false fun _ =>
      s!"[{i}] got {fmt got[i]!}, expected {fmt want[i]!} ({F64.ulpDist got[i]! want[i]!} ulps)"

/-- Compare a float with a golden float. -/
def checkFloat (label : String) (got : Float) (want : Json) (tol : Tol := {}) : TestM Unit := do
  let w ← gFloat want
  check label (near tol got w) fun _ => s!"got {fmt got}, expected {fmt w}"

/-! ## Field outputs -/

/-- A Lean field reduced to what the goldens record. -/
structure FieldOut where
  /-- Julia `size(t)`. -/
  size : List Nat
  /-- The flat fibers. -/
  fiber : FloatArray
  /-- The flat points. -/
  points : FloatArray
  /-- Whether the fibers are a (lazy) range. -/
  isrange : Bool

/-- Summarize a field. -/
def out {M P G F : Type} [FrameBundle M] [Coordinates M P G] [FlatFiber P] [FlatFiber F] [BaseShape M]
    {m : M} (t : TensorField m F) : FieldOut :=
  ⟨BaseShape.shape m, t.data, FrameBundle.pointsFlat m, t.range?.isSome⟩

/-- Compare a field with a golden field (fibers within `tol`; points, size and the lazy-range
flag exactly). Julia errors are skipped. -/
def checkField (label : String) (got : FieldOut) (want : Json) (tol : Tol := {})
    (checkRange : Bool := true) : TestM Unit := do
  if isErr want then return
  let size ← (← jArr (← jField want "size")).mapM jNat
  check s!"{label} size" (got.size == size.toList) fun _ => s!"got {got.size}, expected {size}"
  checkFloats s!"{label} fiber" got.fiber (← gFloats (← jField want "fiber")) tol
  checkFloats s!"{label} points" got.points (← gFloats (← jField want "points"))
  if checkRange then
    let r ← jBool (← jField want "isrange")
    check s!"{label} isrange" (got.isrange == r) fun _ => s!"got {got.isrange}, expected {r}"

/-- Compare a string with a golden string. -/
def checkStr (label : String) (got : String) (want : Json) : TestM Unit := do
  if isErr want then return
  let w ← jStr want
  check label (got == w) fun _ => s!"\n    got      {got}\n    expected {w}"

/-- Flatten fiber values. -/
def flatOf {F : Type} [FlatFiber F] (xs : List F) : FloatArray := xs.foldl FlatFiber.push .empty

end Tests.CartanTests
