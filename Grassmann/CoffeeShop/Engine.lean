import Grassmann.CoffeeShop.Presets
import Grassmann.CoffeeShop.PresetsExtra
import Grassmann.CoffeeShop.PresetsParity
import Grassmann.CoffeeShop.PresetsShowcase
import Grassmann.Eval.ImplicitExpr
import Grassmann.Codegen.GPUInit

/-!
# Pure-Lean CoffeeShop Studio Engine (`Grassmann.CoffeeShop.Engine`)

Manages all **74 CoffeeShop presets** (19 flagship + 28 `PresetsExtra` + 22 `PresetsParity`
+ 5 `PresetsShowcase` Wave 4B physics/relativity/streamline presets), draggable 3D/2D handles,
interactive `@param` sliders (`setParam`), KaTeX LaTeX `formula` + `summary` metadata,
RK4 rigid-body & spherical double-pendulum integration, interactive `#pga3d_slicing` cutting
plane motors, live GA scripts (`LiveScript` v2), `z = f(x, y, t)` surfaces, live user-typed
3D implicit equations (`f(x,y,z,t) = 0` via bytecode-accelerated Kuhn Marching Tetrahedra OR
live `GPUInit` GLSL3/WGSL/MSL raymarching), live parametric 3D surfaces, and marching-triangles
2D implicit contours — emitting canonical `SceneFrame`s with zero GA logic in JS/Swift.

Credits: Steven De Keninck (`enkimute` / `ganja.js`) & Michael Reed (`chakravala` / `Grassmann.jl`).
-/

namespace Grassmann.CoffeeShop

open Grassmann.Scene Grassmann.Scene.Json Grassmann.Eval Grassmann.Eval.ImplicitExpr
open Grassmann.CoffeeShop.PresetsExtra Grassmann.CoffeeShop.PresetsParity
open Grassmann.CoffeeShop.PresetsShowcase Grassmann.Codegen.GPUInit

/-- Serialize all 74 CoffeeShop presets (19 base + 28 extra + 22 parity + 5 showcase) into a single
strictly `Init`-only JSON array for `grassmann_studio_preset_catalog` & `GET /api/presets`. -/
def allPresetCatalogJson : String :=
  let fmt (id title category algebra description sampleCode : String) : String :=
    let (fml, smry) := presetMathMeta id
    objJson #[
      ("id", quote id),
      ("title", quote title),
      ("category", quote category),
      ("algebra", quote algebra),
      ("description", quote description),
      ("sampleCode", quote sampleCode),
      ("formula", quote fml),
      ("summary", quote smry)
    ]
  let baseItems := presetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  let extraItems := extraPresetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  let parityItems := parityPresetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  let showcaseItems := showcasePresetCatalog.map fun p =>
    fmt p.id p.title p.category p.algebra p.description p.sampleCode
  arrJson (((baseItems ++ extraItems) ++ parityItems) ++ showcaseItems)

/-- Total preset count across base + extra + parity + showcase registries (74). -/
def totalPresetCount : Nat :=
  presetCatalog.size + extraPresetCatalog.size + parityPresetCatalog.size + showcasePresetCatalog.size

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
  paramOverrides       : Array (String × Float) := #[]
  sliceMotor           : Option Motor3 := none
  customCamera         : Option CameraState := none
  simTime              : Float := 0.0
  lastValidScriptFrame : Option SceneFrame := none
  -- Persistent RK4 physics state for `pga3d_physics_free_top`
  topMotor             : Motor3 := Motor3.identity
  topOmega             : Vec3   := ⟨0.08, 3.2, 0.05⟩ -- Perturbed intermediate axis => Dzhanibekov flip!
  topTrail             : FloatArray := FloatArray.empty
  -- Persistent RK4 physics state for Wave 4B `pga3d_bouncing_cube` & `pga3d_double_pendulum`
  cubeState            : BouncingCubeState := initBouncingCubeState 2.6
  doublePendulum       : DoublePendulumState := initDoublePendulumState 1.0
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
    paramOverrides := #[],
    sliceMotor := none,
    customCamera := none,
    simTime := 0.0,
    topMotor := Motor3.identity,
    topOmega := ⟨0.08, 3.2, 0.05⟩,
    topTrail := FloatArray.empty,
    cubeState := initBouncingCubeState 2.6,
    doublePendulum := initDoublePendulumState 1.0 }

def setHandle (st : CoffeeShopState) (hid : UInt32) (pos : Vec3) : CoffeeShopState :=
  let next :=
    match st.handles.findIdx? fun kv => kv.1 == hid with
    | some idx => st.handles.set! idx (hid, pos)
    | none     => st.handles.push (hid, pos)
  { st with handles := next }

/-- Update a live `@param` / `slider(...)` value (used by both interactive presets and LiveScript v2). -/
def setParam (st : CoffeeShopState) (name : String) (val : Float) : CoffeeShopState :=
  let nextParams :=
    match st.paramOverrides.findIdx? fun kv => kv.1 == name with
    | some idx => st.paramOverrides.set! idx (name, val)
    | none     => st.paramOverrides.push (name, val)
  let st1 := { st with paramOverrides := nextParams }
  if !st1.useCustom && st1.presetId == "pga3d_bouncing_cube" && name == "spin" then
    let s := max 0.0 (min 8.0 val)
    let curW := st1.cubeState.omega
    let curMag := Vec3.norm curW
    let dir := if curMag > 1e-4 then Vec3.scale (1.0 / curMag) curW else Vec3.normalize ⟨0.72, 0.55, -0.46⟩
    { st1 with cubeState := { st1.cubeState with omega := Vec3.scale s dir } }
  else if !st1.useCustom && st1.presetId == "pga3d_double_pendulum" && name == "length" then
    let l := max 0.4 (min 1.5 val)
    let d := paramVal nextParams "damping" 0.03 0.0 0.35
    let g := paramVal nextParams "gravity" 9.8 1.0 20.0
    { st1 with doublePendulum := stepDoublePendulumRK4 st1.doublePendulum 0.002 l d g }
  else st1

/-- Look up the runnable LiveScript v2 `sampleCode` for any of the 74 registered presets. -/
def presetScriptFor (presetId : String) : String :=
  match presetCatalog.find? (·.id == presetId) with
  | some p => p.sampleCode
  | none =>
    match extraPresetCatalog.find? (·.id == presetId) with
    | some p => p.sampleCode
    | none =>
      match parityPresetCatalog.find? (·.id == presetId) with
      | some p => p.sampleCode
      | none =>
        match showcasePresetCatalog.find? (·.id == presetId) with
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
  let fresh := evalScriptToFrame algebra code #[] st.simTime 0 #[] #[]
  let nextValid :=
    if fresh.diagnostics.isEmpty then some fresh
    else st.lastValidScriptFrame
  { st with
    customAlgebra := algebra, customCode := code,
    handles := #[], coeffOverrides := #[], paramOverrides := #[], eqOverlay := none,
    lastValidScriptFrame := nextValid,
    useCustom := true, useSurface := false, useImplicit := false, useParametric := false }

def setSurface (st : CoffeeShopState) (expr : String)
    (minX maxX minY maxY : Float) (gridN : Nat) : CoffeeShopState :=
  { st with
    surfaceExpr := expr,
    surfaceBounds := (minX, maxX, minY, maxY),
    surfaceGridN := max 8 (min 96 gridN),
    eqOverlay := none,
    useSurface := true, useCustom := false, useImplicit := false, useParametric := false }

def setImplicit (st : CoffeeShopState) (expr : String) (gpuRaymarch : Bool := false)
    (bound : Float := 1.6) (gridN : Nat := 18) : CoffeeShopState :=
  let b := if bound > 0.1 then min 10.0 bound else 1.6
  { st with
    implicitExpr := expr,
    implicitGpuRaymarch := gpuRaymarch,
    implicitBound := b,
    implicitGridN := max 8 (min 36 gridN),
    eqOverlay := none,
    useImplicit := true, useCustom := false, useSurface := false, useParametric := false }

def setParametric (st : CoffeeShopState) (fx fy fz : String)
    (uMin uMax vMin vMax : Float) (nu nv : Nat) : CoffeeShopState :=
  { st with
    paramFx := fx, paramFy := fy, paramFz := fz,
    paramUBounds := (uMin, uMax),
    paramVBounds := (vMin, vMax),
    paramNu := max 8 (min 96 nu),
    paramNv := max 6 (min 64 nv),
    eqOverlay := none,
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

/-- Advance simulation clock + RK4 physics integrators when active. -/
def stepTick (st : CoffeeShopState) (dt timeSec : Float) : CoffeeShopState :=
  let clampedDt := max 0.001 (min 0.05 dt)
  let nextT := if timeSec > 0.0 then timeSec else st.simTime + clampedDt
  let inPreset := !st.useCustom && !st.useSurface && !st.useImplicit && !st.useParametric
  if inPreset && st.presetId == "pga3d_physics_free_top" then
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
  else if inPreset && st.presetId == "pga3d_bouncing_cube" then
    let g := paramVal st.paramOverrides "gravity" 9.8 0.5 20.0
    let e := paramVal st.paramOverrides "restitution" 0.78 0.1 0.98
    let sp := paramVal st.paramOverrides "spin" 2.6 0.0 8.0
    let cube1 := stepBouncingCubeRK4 st.cubeState clampedDt g e sp
    { st with simTime := nextT, cubeState := cube1 }
  else if inPreset && st.presetId == "pga3d_double_pendulum" then
    let l := paramVal st.paramOverrides "length" 1.0 0.4 1.5
    let d := paramVal st.paramOverrides "damping" 0.03 0.0 0.35
    let g := paramVal st.paramOverrides "gravity" 9.8 1.0 20.0
    let dp1 := stepDoublePendulumRK4 st.doublePendulum clampedDt l d g
    { st with simTime := nextT, doublePendulum := dp1 }
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
      formula := "f(x, y, z, t) = 0,\\qquad \\mathbf{p}_{k+1} = \\mathbf{p}_k + \\tfrac{f(\\mathbf{p}_k)}{\\|\\nabla f\\|}\\,\\mathbf{d}",
      summary := s!"Real-time Lean-compiled GLSL3/WGSL/MSL sphere-tracing raymarcher for `{exprStr} = 0`.",
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

/-- Emit the live `SceneFrame` for the active CoffeeShop preset (all 74 presets),
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
          presetId := "surface_3d", title := s!"z = {st.surfaceExpr}",
          formula := "z = f(x, y, t),\\qquad \\mathbf{n} = \\star(T_x \\wedge T_y)",
          summary := s!"Animated 3D heightfield surface `z = {st.surfaceExpr}` with analytical forward-AD tangent normals." }
      match evalSurfaceMesh st.surfaceExpr st.simTime minX maxX minY maxY st.surfaceGridN 9001 with
      | .ok m =>
        { base with
          meshAssets := #[m]
          meshRefs := #[{ meshId := m.meshId, dirtyHash := m.dirtyHash,
                          color := RGBA.white, useVertexColors := true }] }
      | .error err => { base with diagnostics := #[err] }
    else if st.useCustom then
      let fr := evalScriptToFrame st.customAlgebra st.customCode st.handles st.simTime frameSeq st.coeffOverrides st.paramOverrides
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
            | none =>
              match buildShowcasePreset other st.cubeState st.doublePendulum st.handles st.paramOverrides frameSeq st.simTime with
              | some fr => fr
              | none => buildPga3dSlicing st.handles st.sliceMotor frameSeq st.simTime
      let withScript := if rawP.script.isEmpty then { rawP with script := presetScriptFor st.presetId } else rawP
      let (defFml, defSmry) := presetMathMeta withScript.presetId
      { withScript with
        formula := if withScript.formula.isEmpty then defFml else withScript.formula,
        summary := if withScript.summary.isEmpty then defSmry else withScript.summary }
  let f1 := match st.customCamera with
    | some cam => { f0 with camera := cam }
    | none     => f0
  match st.eqOverlay with
  | some ov => { f1 with contourOverlay := some ov }
  | none    => f1

end Grassmann.CoffeeShop
