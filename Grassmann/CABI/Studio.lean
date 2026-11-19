/-
  Grassmann/CABI/Studio.lean — Strictly Init-only IO.Ref Session Registry
  backing `Grassmann.CABI` and `Grassmann.Server` via the full `Grassmann.Studio`
  engine (19 CoffeeShop presets, sculpted bunny `#pga3d_slicing`, 16 Wedge 2D+3D
  levels, GA script parser/evaluator, AD surfaces, marching-triangles contours,
  GAlculator, R3 rational rotors, and WGSL/GLSL/MSL OPNS shader codegen).
-/
import Grassmann.Studio

namespace Grassmann.CABI.Studio

open Grassmann.Studio

private structure SessionSlot where
  id    : UInt64
  state : StudioSession
  deriving Inhabited

private structure SessionRegistry where
  nextId : UInt64 := 1
  slots  : Array SessionSlot := #[]
  deriving Inhabited

initialize studioRegistry : IO.Ref SessionRegistry ← IO.mkRef {}

/-- Create a new `StudioSession` initialized to `#pga3d_slicing` (sculpted bunny + contour). -/
def createSession : IO UInt64 := do
  let reg ← studioRegistry.get
  let id := reg.nextId
  let initial := Grassmann.Studio.create
  studioRegistry.set {
    nextId := id + 1,
    slots := reg.slots.push { id, state := initial }
  }
  return id

/-- Destroy an active session by ID. -/
def destroySession (sid : UInt64) : IO Unit := do
  let reg ← studioRegistry.get
  studioRegistry.set { reg with slots := reg.slots.filter (fun s => s.id != sid) }

private def findSlotIdx (slots : Array SessionSlot) (sid : UInt64) : Option Nat := Id.run do
  for i in [:slots.size] do
    if slots[i]!.id == sid then return some i
  return none

/-- Dispatch a packed binary `GSIR` `InputEvent` and return `(status, frameBytes)`.
Status: `0` = OK, `-1` = BAD_HANDLE, `-2` = BAD_INPUT. -/
def dispatchBin (sid : UInt64) (eventBuf : ByteArray) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    let slot := reg.slots[idx]!
    match Grassmann.Studio.dispatchBin slot.state eventBuf with
    | .error _ => return (-2, ByteArray.empty)
    | .ok (nextState, frame) =>
      let slots' := reg.slots.set! idx { slot with state := nextState }
      studioRegistry.set { reg with slots := slots' }
      return (0, frame)

/-- Dispatch a JSON `InputEvent` and return `(status, frameBytes)`. -/
def dispatchJson (sid : UInt64) (eventJson : String) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    let slot := reg.slots[idx]!
    match Grassmann.Studio.dispatchJson slot.state eventJson with
    | .error _ => return (-2, ByteArray.empty)
    | .ok (nextState, frame) =>
      let slots' := reg.slots.set! idx { slot with state := nextState }
      studioRegistry.set { reg with slots := slots' }
      return (0, frame)

/-- Idempotent read of the cached `GSIR` v1 binary frame (zero state mutation!). -/
def getCachedFrame (sid : UInt64) : IO (Int32 × ByteArray) := do
  let reg ← studioRegistry.get
  match findSlotIdx reg.slots sid with
  | none => return (-1, ByteArray.empty)
  | some idx =>
    return (0, Grassmann.Studio.getLastFrame reg.slots[idx]!.state)

/-- Return the complete JSON preset catalog (all 77 CoffeeShop presets). -/
def getPresetCatalogJson : String :=
  Grassmann.Studio.presetCatalogJson

/-- Return the complete 6-stop Guided GA Tour catalog JSON (`0..5`). -/
def getTourCatalogJson : String :=
  Grassmann.Studio.tourCatalogJson

end Grassmann.CABI.Studio
