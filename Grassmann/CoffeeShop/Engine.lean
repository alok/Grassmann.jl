import Grassmann.CoffeeShop.Presets
import Grassmann.CoffeeShop.PresetsExtra
import Grassmann.CoffeeShop.PresetsParity
import Grassmann.Eval.ImplicitExpr
import Grassmann.Codegen.GPUInit

/-!
# Pure-Lean CoffeeShop Studio Engine (`Grassmann.CoffeeShop.Engine`)

Manages all **69 CoffeeShop presets** (19 flagship + 28 `PresetsExtra` + 22 `PresetsParity`,
100% parity with the 64-entry `ganja.js` catalog), draggable 3D/2D handles, RK4 rigid-body
integration, interactive `#pga3d_slicing` cutting plane motors, live GA scripts,
`z = f(x, y, t)` surfaces, live user-typed 3D implicit equations (`f(x,y,z,t) = 0` via Kuhn
Marching Tetrahedra OR live `GPUInit` GLSL3/WGSL/MSL raymarching), live parametric 3D
surfaces, and marching-triangles 2D implicit contours — emitting canonical `SceneFrame`s
with zero GA logic in JS/Swift.

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.CoffeeShop

open Grassmann.Scene Grassmann.Scene.Json Grassmann.Eval Grassmann.Eval.ImplicitExpr
open Grassmann.CoffeeShop.PresetsExtra Grassmann.CoffeeShop.PresetsParity
open Grassmann.Codegen.GPUInit

/-- Serialize all 69 CoffeeShop presets (19 base + 28 extra + 22 parity) into a single
strictly `Init`-only JSON array for `grassmann_studio_preset_catalog` & `GET /api/presets`. -/
def allPresetCatalogJson : String :=
  let fmt (id title category algebra description sampleCode : String) : String :=
    objJson #[
      ("id", quote id),
      ("title", quote title),
      ("category", quote category),
      ("algebra", quote algebra),
      ("description", quote description),
      ("sampleCode", quote sampleCode)
    ]
  let baseItems := presetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  let extraItems := extraPresetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  let parityItems := parityPresetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  arrJson ((baseItems ++ extraItems) ++ parityItems)

/-- Total preset count across base + extra + parity registries (69). -/
def totalPresetCount : Nat :=
  presetCatalog.size + extraPresetCatalog.size + parityPresetCatalog.size

/-- Mutable state of the CoffeeShop & Surface studio workspace. -/
structure CoffeeShopState where
  presetId             : String := "pga3d_slicing"
  customAlgebra        : String := "PGA3"
  customCode           : String := ""
  useCustom            : Bool   := false
  surfaceExpr          : String := "0.55 * sin(1.8*x + t) * cos(1.8*y)"
  surfaceBounds        : Float × Float × Float × Float := (-2.0, 2.0, -2.0, 2.0)
  surfaceGridN         : Nat    := 40
  useSurface           : Bool   := false
  implicitExpr         : String := "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)"
  implicitGpuRaymarch  : Bool   := false
  implicitBound        : Float  := 1.6
  implicitGridN        : Nat    := 18
  useImplicit          : Bool   := false
  paramFx              : String := "(1.1 + 0.42*cos(v))*cos(u)"
  paramFy              : String := "0.42*sin(v)"
  paramFz              : String := "(1.1 + 0.42*cos(v))*sin(u)"
  paramUBounds         : Float × Float := (0.0, 6.283185307179586)
  paramVBounds         : Float × Float := (0.0, 6.283185307179586)
  paramNu              : Nat    := 40
  paramNv              : Nat    := 24
  useParametric        : Bool   := false
  eqOverlay            : Option ContourOverlay := none
  handles              : Array (UInt32 × Vec3) := #[]
  coeffOverrides       : Array (UInt32 × UInt32 × Float) := #[]
  sliceMotor           : Option Motor3 := none
  customCamera         : Option CameraState := none
  simTime              : Float := 0.0
  lastValidScriptFrame : Option SceneFrame := none
  -- Persistent RK4 physics state for `pga3d_physics_free_top`
  topMotor             : Motor3 := Motor3.identity
  topOmega             : Vec3   := ⟨0.08, 3.2, 0.05⟩ -- Perturbed intermediate axis => Dzhanibekov flip!
  topTrail             : FloatArray := FloatArray.empty
  deriving Inhabited

def CoffeeShopState.init (presetId : String := "pga3d_slicing") : CoffeeShopState :=
  { presetId }

def loadPreset (st : CoffeeShopState) (presetId : String) : CoffeeShopState :=
  { st with
    presetId,
    useCustom := false,
    useSurface := false,
    useImplicit := false,
    useParametric := false,
    eqOverlay := none,
    handles := #[],
    sliceMotor := none,
    customCamera := none,
    simTime := 0.0,
    topMotor := Motor3.identity,
    topOmega := ⟨0.08, 3.2, 0.05⟩,
    topTrail := FloatArray.empty }

def setHandle (st : CoffeeShopState) (hid : UInt32) (pos : Vec3) : CoffeeShopState :=
  let next :=
    match st.handles.findIdx? fun kv => kv.1 == hid with
    | some idx => st.handles.set! idx (hid, pos)
    | none     => st.handles.push (hid, pos)
  { st with handles := next }

/-- Look up the runnable LiveScript v2 `sampleCode` for any of the 69 registered presets. -/
def presetScriptFor (presetId : String) : String :=
  match presetCatalog.find? (·.id == presetId) with
  | some p => p.sampleCode
  | none =>
    match extraPresetCatalog.find? (·.id == presetId) with
    | some p => p.sampleCode
    | none =>
      match parityPresetCatalog.find? (·.id == presetId) with
      | some p => p.sampleCode
      | none => ""

/-- Live coefficient edit from CoffeeShop's `inspect stash` table: records override and
maps blade edits directly onto live script multivectors (when in script mode) OR
interactive handles (`0..2` → `x/y/z`) / `#pga3d_slicing` plane! -/
def setCoeffOverride (st : CoffeeShopState) (entryIdx bladeIdx : UInt32) (val : Float) :
    CoffeeShopState :=
  let nextOv :=
    match st.coeffOverrides.findIdx? fun x => x.1 == entryIdx && x.2.1 == bladeIdx with
    | some idx => st.coeffOverrides.set! idx (entryIdx, bladeIdx, val)
    | none     => st.coeffOverrides.push (entryIdx, bladeIdx, val)
  if st.useCustom then
    { st with coeffOverrides := nextOv }
  else
    let cur := hPos st.handles entryIdx Vec3.zero
    let nextPos : Vec3 :=
      match bladeIdx.toNat % 3 with
      | 0 => { cur with x := val }
      | 1 => { cur with y := val }
      | _ => { cur with z := val }
    let st1 := setHandle { st with coeffOverrides := nextOv } entryIdx nextPos
    if st.presetId == "pga3d_slicing" && entryIdx == 0 then
      { st1 with sliceMotor := none }
    else st1

def setScript (st : CoffeeShopState) (algebra code : String) : CoffeeShopState :=
  -- Evaluate once immediately to update `lastValidScriptFrame` when valid (never losing last good scene on syntax error!)
  let fresh := evalScriptToFrame algebra code #[] st.simTime 0 #[]
  let nextValid :=
    if fresh.diagnostics.isEmpty then some fresh
    else st.lastValidScriptFrame
  { st with
    customAlgebra := algebra, customCode := code,
    handles := #[], coeffOverrides := #[],
    lastValidScriptFrame := nextValid,
    useCustom := true, useSurface := false, useImplicit := false, useParametric := false }

def setSurface (st : CoffeeShopState) (expr : String)
    (minX maxX minY maxY : Float) (gridN : Nat) : CoffeeShopState :=
  { st with
    surfaceExpr := expr,
    surfaceBounds := (minX, maxX, minY, maxY),
    surfaceGridN := max 8 (min 96 gridN),
    useSurface := true, useCustom := false, useImplicit := false, useParametric := false }

def setImplicit (st : CoffeeShopState) (expr : String) (gpuRaymarch : Bool := false)
    (bound : Float := 1.6) (gridN : Nat := 18) : CoffeeShopState :=
  let b := if bound > 0.1 then min 10.0 bound else 1.6
  { st with
    implicitExpr := expr,
    implicitGpuRaymarch := gpuRaymarch,
    implicitBound := b,
    implicitGridN := max 8 (min 36 gridN),
    useImplicit := true, useCustom := false, useSurface := false, useParametric := false }

def setParametric (st : CoffeeShopState) (fx fy fz : String)
    (uMin uMax vMin vMax : Float) (nu nv : Nat) : CoffeeShopState :=
  { st with
    paramFx := fx, paramFy := fy, paramFz := fz,
    paramUBounds := (uMin, uMax),
    paramVBounds := (vMin, vMax),
    paramNu := max 8 (min 96 nu),
    paramNv := max 6 (min 64 nv),
    useParametric := true, useCustom := false, useSurface := false, useImplicit := false }

def setEquations (st : CoffeeShopState) (eqs : Array String)
    (minX maxX minY maxY : Float) (gridN : Nat) : CoffeeShopState :=
  match evalEquationsToOverlay eqs minX maxX minY maxY gridN with
  | .ok ov => { st with eqOverlay := some ov }
  | .error _ => st

def setSlicePlane (st : CoffeeShopState) (m : Motor3) : CoffeeShopState :=
  { st with sliceMotor := some (Motor3.normalize m) }

def setCamera (st : CoffeeShopState) (m : Motor3) (fovDeg distance : Float) : CoffeeShopState :=
  { st with customCamera := some { motor := m, fovDeg, distance } }

/-- Advance simulation clock + RK4 physics integrator when active. -/
def stepTick (st : CoffeeShopState) (dt timeSec : Float) : CoffeeShopState :=
  let clampedDt := max 0.001 (min 0.05 dt)
  let nextT := if timeSec > 0.0 then timeSec else st.simTime + clampedDt
  if st.presetId == "pga3d_physics_free_top" && !st.useCustom && !st.useSurface &&
     !st.useImplicit && !st.useParametric then
    let (m1, w1) := stepFreeTopRK4 st.topMotor st.topOmega clampedDt
    let tip := Motor3.applyPoint m1 ⟨0.0, 1.15, 0.0⟩
    let trail0 :=
      if st.topTrail.size ≥ 180 * 3 then
        -- Ring-trim oldest 3 floats
        let rec shift (i : Nat) (acc : FloatArray) : FloatArray :=
          if i < st.topTrail.size then shift (i + 1) (acc.push (st.topTrail.get! i)) else acc
        shift 3 (FloatArray.emptyWithCapacity (180 * 3))
      else st.topTrail
    let trail1 := trail0.push tip.x |>.push tip.y |>.push tip.z
    { st with simTime := nextT, topMotor := m1, topOmega := w1, topTrail := trail1 }
  else
    { st with simTime := nextT }

/-- Build a GPU-raymarched implicit 3D frame via strictly `Init`-only `GPUInit`
(GLSL 300 es + WGSL + Metal MSL). -/
private def buildImplicitGpuFrame (exprStr : String) (seq : UInt64) (t : Float) : SceneFrame :=
  let base : SceneFrame :=
    { frameSeq := seq, simTime := t, mode := .surface, is2D := false,
      gridEnabled := true, darkTheme := true, gridSize := 2.2,
      algebra := { name := "R3", p := 3, q := 0, r := 0,
                   basisNames := #["1","e1","e2","e3","e12","e13","e23","I"],
                   basisMetric := #[1,1,1,1,-1,-1,-1,-1] },
      presetId := "implicit_gpu", title := s!"GPU Implicit: {exprStr} = 0",
      camera := { motor := Motor3.orbitCamera 0.55 (-0.32) 4.6, fovDeg := 45.0, distance := 4.6 } }
  match compileImplicitExprToGpu exprStr "implicit_gpu" with
  | .ok shader =>
    { base with
      opnsShaders := #[shader],
      opnsUniforms := #[{
        shaderIdx := 0, grade := 0, coeffs := FloatArray.empty,
        thresh := 0.015, maxSteps := 96, stepSize := 0.01,
        color := ⟨0.36, 0.78, 1.0, 0.96⟩, isIPNS := false }],
      inspect := #[{ idx := 0, name := "GPU Raymarcher", grade := 0,
                     formatted := s!"{exprStr} = 0 · WGSL+GLSL3+MSL ({shader.hash})" }] }
  | .error err =>
    { base with diagnostics := #[err] }

/-- Emit the live `SceneFrame` for the active CoffeeShop preset (all 69 presets),
custom GA script, `z = f(x,y,t)` surface, 3D implicit equation (mesh or GPU raymarcher),
or 3D parametric surface. -/
def toSceneFrame (st : CoffeeShopState) (frameSeq : UInt64 := 0) : SceneFrame :=
  let f0 : SceneFrame :=
    if st.useImplicit then
      if st.implicitGpuRaymarch then
        buildImplicitGpuFrame st.implicitExpr frameSeq st.simTime
      else
        let b := st.implicitBound
        evalImplicitExprToFrame st.implicitExpr frameSeq st.simTime
          ⟨-b, -b, -b⟩ ⟨b, b, b⟩ st.implicitGridN
    else if st.useParametric then
      let (uMin, uMax) := st.paramUBounds
      let (vMin, vMax) := st.paramVBounds
      evalParametricExprToFrame st.paramFx st.paramFy st.paramFz frameSeq st.simTime
        uMin uMax vMin vMax st.paramNu st.paramNv
    else if st.useSurface then
      let (minX, maxX, minY, maxY) := st.surfaceBounds
      let (algName, V, p, q, r, witt) := resolveAlgebra "R3"
      let base : SceneFrame :=
        { frameSeq, simTime := st.simTime, mode := .surface, is2D := false,
          algebra := algebraMetaOf algName V p q r witt,
          presetId := "surface_3d", title := s!"z = {st.surfaceExpr}" }
      match evalSurfaceMesh st.surfaceExpr st.simTime minX maxX minY maxY st.surfaceGridN 9001 with
      | .ok m =>
        { base with
          meshAssets := #[m]
          meshRefs := #[{ meshId := m.meshId, dirtyHash := m.dirtyHash,
                          color := RGBA.white, useVertexColors := true }] }
      | .error err => { base with diagnostics := #[err] }
    else if st.useCustom then
      let fr := evalScriptToFrame st.customAlgebra st.customCode st.handles st.simTime frameSeq st.coeffOverrides
      if !fr.diagnostics.isEmpty then
        match st.lastValidScriptFrame with
        | some prev =>
          { prev with frameSeq, simTime := st.simTime, script := st.customCode, diagnostics := fr.diagnostics }
        | none => fr
      else fr
    else
      let rawP :=
        match st.presetId with
        | "pga3d_slicing"            => buildPga3dSlicing st.handles st.sliceMotor frameSeq st.simTime
        | "pga3d_points_and_lines"   => buildPga3dPointsAndLines st.handles frameSeq st.simTime
        | "pga3d_physics_free_top"   => buildPga3dFreeTop st.topMotor st.topOmega st.topTrail frameSeq st.simTime
        | "pga3d_origami"            => buildPga3dOrigami frameSeq st.simTime
        | "pga3d_motor_orbits"       => buildPga3dMotorOrbits frameSeq st.simTime
        | "pga3d_icosahedron"        => buildPga3dIcosahedron frameSeq st.simTime
        | "pga3d_skinning"           => buildPga3dSkinning frameSeq st.simTime
        | "pga3d_objects"            => buildPga3dObjects frameSeq st.simTime
        | "cga3d_intersections"      => buildCga3dIntersections st.handles frameSeq st.simTime
        | "cga3d_spheres_apollonius" => buildCga3dSpheresApollonius st.handles frameSeq st.simTime
        | "cga3d_opns_cyclide"       => buildCga3dOpnsCyclide frameSeq st.simTime
        | "pga2d_euler_line"         => buildPga2dEulerLine st.handles frameSeq st.simTime
        | "pga2d_inverse_kinematics" => buildPga2dIK st.handles frameSeq st.simTime
        | "pga2d_desargues_theorem"  => buildPga2dDesargues st.handles frameSeq st.simTime
        | "sta_lorentz_boost"        => buildStaLorentzBoost st.handles frameSeq st.simTime
        | "sta_maxwell_em"           => buildStaMaxwellEM frameSeq st.simTime
        | "r3_rational_rotor"        => buildR3RationalRotor st.handles frameSeq st.simTime
        | "dual_autodiff_surface"    => buildDualAutodiffSurface st.handles frameSeq st.simTime
        | "complex_mobius_orbit"     => buildComplexMobius st.handles frameSeq st.simTime
        | other =>
          match buildExtraPreset other st.handles frameSeq st.simTime with
          | some fr => fr
          | none =>
            match buildParityPreset other st.handles frameSeq st.simTime with
            | some fr => fr
            | none => buildPga3dSlicing st.handles st.sliceMotor frameSeq st.simTime
      if rawP.script.isEmpty then { rawP with script := presetScriptFor st.presetId } else rawP
  let f1 := match st.customCamera with
    | some cam => { f0 with camera := cam }
    | none     => f0
  match st.eqOverlay with
  | some ov => { f1 with contourOverlay := some ov }
  | none    => f1

end Grassmann.CoffeeShop
