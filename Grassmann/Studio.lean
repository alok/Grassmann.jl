import Grassmann.Scene
import Grassmann.Eval
import Grassmann.Wedge
import Grassmann.CoffeeShop
import Grassmann.Codegen

/-!
# Unified Pure-Lean Studio Session Dispatcher (`Grassmann.Studio`)

Single canonical entry point for both:
- Native macOS / visionOS C ABI (`grassmann_studio_{create,destroy,dispatch_bin,dispatch_json,get_frame}`)
- Emscripten WASM & HTTP/WS `ga-server` for the Web 3D Studio.

Implements ALL `docs/SCENE_IR_V1.md` + `#17` guarantees:
- **Zero state double-mutation**: `dispatchBin`/`dispatchJson` apply an event ONCE and cache the
  encoded `GSIR` v1 frame inside `StudioSession.lastEncoded`; `getLastFrame` returns it idempotently!
- **Delta `MESH_ASSETS` caching**: tracks uploaded `(meshId, dirtyHash)` pairs and omits unchanged
  meshes on hot `Tick`/`DragHandle` frames (re-emitting everything on `snapshot` / `forceFullSnapshot`).
- **Delta `metaJson` & `opnsShaders` caching**: omits unchanged `metaJson` (`metaJsonLen = 0`) and
  already-sent shader bodies on hot frames for 90fps visionOS / 60fps Web zero-parse updates!
-/

namespace Grassmann.Studio

open Grassmann.Scene Grassmann.Scene.Binary Grassmann.Scene.Json
open Grassmann.Eval Grassmann.Eval.Calc Grassmann.Wedge Grassmann.CoffeeShop

/-- Active top-level workspace mode inside a `StudioSession`. -/
inductive ActiveApp where
  | coffeeShop
  | wedge
  | calculator
  deriving DecidableEq, Repr, Inhabited

/-- Complete stateful studio session (pure immutable value; C ABI / server stores in `IO.Ref`). -/
structure StudioSession where
  active            : ActiveApp := .coffeeShop
  coffee            : CoffeeShopState := CoffeeShopState.init "pga3d_slicing"
  wedge             : WedgeState := Wedge.initState false
  calcState         : CalcState := CalcState.init "STA"
  frameSeq          : UInt64 := 0
  randomSeedCounter : UInt64 := 1
  sentMeshHashes    : Array (UInt64 × UInt64) := #[]
  sentShaderHash    : Array String := #[]
  lastMetaDigest    : UInt64 := 0
  lastEncoded       : ByteArray := ByteArray.empty
  deriving Inhabited

/-- Fast 64-bit FNV-1a digest of a `String` for detecting unchanged `metaJson`. -/
private def fnvString (s : String) : UInt64 :=
  let bytes := s.toUTF8
  let prime : UInt64 := 1099511628211
  let rec go (i : Nat) (h : UInt64) : UInt64 :=
    if i < bytes.size then go (i + 1) ((h ^^^ (bytes.get! i).toUInt64) * prime) else h
  go 0 14695981039346656037

/-- Filter `meshAssets` against already-uploaded `(meshId, dirtyHash)` pairs unless `forceFull`. -/
private def filterDeltaMeshes (sent : Array (UInt64 × UInt64)) (assets : Array MeshAsset)
    (forceFull : Bool) : Array MeshAsset × Array (UInt64 × UInt64) := Id.run do
  let mut cache := if forceFull then #[] else sent
  let mut toSend : Array MeshAsset := #[]
  for m in assets do
    let already := cache.any fun (id, h) => id == m.meshId && h == m.dirtyHash
    if !already then
      toSend := toSend.push m
      match cache.findIdx? fun (id, _) => id == m.meshId with
      | some idx => cache := cache.set! idx (m.meshId, m.dirtyHash)
      | none     => cache := cache.push (m.meshId, m.dirtyHash)
  return (toSend, cache)

/-- Strip already-sent shader source bodies (leaving `{ hash, wgsl:"", glsl:"", msl:"" }`) unless `forceFull`. -/
private def filterDeltaShaders (sent : Array String) (shaders : Array OpnsShaderSource)
    (forceFull : Bool) : Array OpnsShaderSource × Array String := Id.run do
  let mut cache := if forceFull then #[] else sent
  let mut out : Array OpnsShaderSource := #[]
  for s in shaders do
    if cache.contains s.hash then
      out := out.push { hash := s.hash, wgsl := "", glsl := "", msl := "" }
    else
      cache := cache.push s.hash
      out := out.push s
  return (out, cache)

/-- Render current `StudioSession` to `SceneFrame`, apply delta compression, and cache `GSIR` bytes. -/
def renderAndCache (st : StudioSession) (forceFull : Bool := false) : StudioSession :=
  let nextSeq := st.frameSeq + 1
  let rawFrame : SceneFrame :=
    match st.active with
    | .coffeeShop => CoffeeShop.toSceneFrame st.coffee nextSeq
    | .wedge      => Wedge.toSceneFrame st.wedge nextSeq st.coffee.simTime
    | .calculator => Calc.toSceneFrame st.calcState nextSeq st.coffee.simTime
  let (deltaMeshes, nextMeshCache) := filterDeltaMeshes st.sentMeshHashes rawFrame.meshAssets forceFull
  let (deltaShaders, nextShaderCache) := filterDeltaShaders st.sentShaderHash rawFrame.opnsShaders forceFull
  let frame : SceneFrame := { rawFrame with meshAssets := deltaMeshes, opnsShaders := deltaShaders }
  let labelsTbl := Json.buildLabelTable frame
  let metaDigest := fnvString (Json.toMetaJson frame labelsTbl)
  let includeMeta := forceFull || metaDigest != st.lastMetaDigest || st.lastEncoded.isEmpty
  let encoded := Binary.encodeFrame frame includeMeta
  { st with
    frameSeq       := nextSeq
    sentMeshHashes := nextMeshCache
    sentShaderHash := nextShaderCache
    lastMetaDigest := metaDigest
    lastEncoded    := encoded }

/-- Create a fresh studio session initialized to the flagship `#pga3d_slicing` preset
with its initial `GSIR` v1 frame pre-cached. -/
def create : StudioSession :=
  renderAndCache {} true

/-- Return the unified catalog of ALL 77 CoffeeShop presets (19 base + 28 extra + 22 parity + 8 showcase)
as a strictly `Init`-only JSON array string. -/
def presetCatalogJson : String :=
  CoffeeShop.allPresetCatalogJson

/-- Return the curated 6-stop interactive Guided GA Tour catalog (`0..5`) as a strictly `Init`-only
JSON array string (single source of truth for Web Studio & Apple Vision Pro / macOS). -/
def tourCatalogJson : String :=
  CoffeeShop.Tour.tourCatalogJson

/-- Apply a typed `InputEvent` ONCE, re-render, and cache the resulting `GSIR` v1 binary frame. -/
def dispatchEvent (st : StudioSession) (ev : InputEvent) (forceSnap : Bool := false) :
    StudioSession :=
  let (st1, forceFull) :=
    match ev with
    | .dragHandle hid pos =>
      ({ st with coffee := CoffeeShop.setHandle st.coffee hid pos }, forceSnap)
    | .tick dt t =>
      match st.active with
      | .coffeeShop => ({ st with coffee := CoffeeShop.stepTick st.coffee dt t }, forceSnap)
      | .wedge      => ({ st with wedge := Wedge.stepTick st.wedge dt }, forceSnap)
      | .calculator => ({ st with coffee := { st.coffee with simTime := t } }, forceSnap)
    | .evalScript alg code =>
      ({ st with active := .coffeeShop, coffee := CoffeeShop.setScript st.coffee alg code }, true)
    | .evalSurface expr minX maxX minY maxY gridN =>
      ({ st with active := .coffeeShop,
                 coffee := CoffeeShop.setSurface st.coffee expr minX maxX minY maxY gridN.toNat }, true)
    | .editCoeff ei bi val =>
      ({ st with coffee := CoffeeShop.setCoeffOverride st.coffee ei bi val }, true)
    | .loadPreset id =>
      if id == "wedge_2d" || id == "game_wedge" then
        ({ st with active := .wedge, wedge := Wedge.initState false }, true)
      else if id == "wedge_3d" then
        ({ st with active := .wedge, wedge := Wedge.initState true }, true)
      else if id == "calculator" || id == "galculator" then
        ({ st with active := .calculator }, true)
      else
        ({ st with active := .coffeeShop, coffee := CoffeeShop.loadPreset st.coffee id }, true)
    | .wedgeGesture idA idB dirA dirB holdA holdB isPrev =>
      -- Strictly mode-gated: never let an accidental tap/drag in CoffeeShop/Calculator hijack into Wedge!
      if st.active == .wedge then
        ({ st with wedge := Wedge.stepGesture st.wedge idA idB dirA dirB holdA holdB isPrev }, forceSnap)
      else
        (st, false)
    | .wedgeAction act arg =>
      ({ st with active := .wedge, wedge := Wedge.stepAction st.wedge act arg }, true)
    | .calcKey key =>
      ({ st with active := .calculator, calcState := Calc.stepKey st.calcState key }, true)
    | .calcEval mode expr =>
      ({ st with active := .calculator, calcState := Calc.evalDirect st.calcState mode expr }, true)
    | .setCamera m fov dist =>
      match st.active with
      | .wedge => ({ st with wedge := Wedge.setCamera st.wedge m fov dist }, forceSnap)
      | _      => ({ st with coffee := CoffeeShop.setCamera st.coffee m fov dist }, forceSnap)
    | .slicePlane m =>
      ({ st with active := .coffeeShop, coffee := CoffeeShop.setSlicePlane st.coffee m }, forceSnap)
    | .evalEquations eqs minX maxX minY maxY gridN =>
      ({ st with active := .coffeeShop,
                 coffee := CoffeeShop.setEquations st.coffee eqs minX maxX minY maxY gridN.toNat }, true)
    | .evalImplicit expr gpuRay bound gridN =>
      ({ st with active := .coffeeShop,
                 coffee := CoffeeShop.setImplicit st.coffee expr gpuRay bound gridN.toNat }, true)
    | .evalParametric fx fy fz uMin uMax vMin vMax nu nv =>
      ({ st with active := .coffeeShop,
                 coffee := CoffeeShop.setParametric st.coffee fx fy fz uMin uMax vMin vMax nu.toNat nv.toNat }, true)
    | .wedgeTutorial id =>
      ({ st with active := .wedge, wedge := Wedge.loadTutorial id }, true)
    | .wedgeRandom is3D difficulty seed =>
      let effectiveSeed := if seed == 0 then st.randomSeedCounter else seed
      ({ st with active := .wedge,
                 randomSeedCounter := st.randomSeedCounter + 1,
                 wedge := Wedge.loadRandomChallenge is3D difficulty.toNat effectiveSeed }, true)
    | .setParam name val =>
      ({ st with coffee := CoffeeShop.setParam st.coffee name val }, forceSnap)
    | .loadTourStop idx =>
      let stop := CoffeeShop.Tour.getTourStop idx.toNat
      if stop.mode == "wedge" || stop.presetId == "wedge_2d" then
        ({ st with active := .wedge, wedge := Wedge.initState false }, true)
      else if stop.presetId == "wedge_3d" then
        ({ st with active := .wedge, wedge := Wedge.initState true }, true)
      else
        ({ st with active := .coffeeShop, coffee := CoffeeShop.loadPreset st.coffee stop.presetId }, true)
    | .resetTime =>
      match st.active with
      | .coffeeShop => ({ st with coffee := CoffeeShop.resetTime st.coffee }, true)
      | .wedge      => ({ st with wedge := { st.wedge with elapsedSec := 0.0, timerStarted := false } }, true)
      | .calculator => ({ st with coffee := { st.coffee with simTime := 0.0 } }, true)
    | .seekTime timeSec =>
      let t := max 0.0 timeSec
      match st.active with
      | .coffeeShop => ({ st with coffee := CoffeeShop.seekTime st.coffee t }, forceSnap)
      | .wedge      => ({ st with wedge := { st.wedge with elapsedSec := t } }, forceSnap)
      | .calculator => ({ st with coffee := { st.coffee with simTime := t } }, forceSnap)
    | .snapshot =>
      (st, true)
  renderAndCache st1 forceFull

/-- Fast binary dispatch (`GSIR` InputEvent → cached `GSIR` v1 `ByteArray`). -/
def dispatchBin (st : StudioSession) (eventBuf : ByteArray) :
    Except String (StudioSession × ByteArray) := do
  let (ev, forceSnap) ← Binary.decodeInputEventBin eventBuf
  let stNext := dispatchEvent st ev forceSnap
  return (stNext, stNext.lastEncoded)

/-- JSON control dispatch (JSON InputEvent → cached `GSIR` v1 `ByteArray`). -/
def dispatchJson (st : StudioSession) (eventJson : String) :
    Except String (StudioSession × ByteArray) := do
  let ev ← Json.parseInputEventJson eventJson
  let stNext := dispatchEvent st ev false
  return (stNext, stNext.lastEncoded)

/-- Idempotent read of the cached `GSIR` v1 frame (ZERO state mutation — solves #17 item 2!). -/
@[inline] def getLastFrame (st : StudioSession) : ByteArray := st.lastEncoded

end Grassmann.Studio
