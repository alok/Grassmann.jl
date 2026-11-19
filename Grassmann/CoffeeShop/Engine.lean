import Grassmann.CoffeeShop.Presets

/-!
# Pure-Lean CoffeeShop Studio Engine (`Grassmann.CoffeeShop.Engine`)

Manages active preset state, draggable 3D/2D handles, RK4 rigid-body integration,
interactive `#pga3d_slicing` cutting plane motors, live GA scripts, `z = f(x, y, t)`
surfaces, and marching-triangles implicit equation systems — emitting canonical
`SceneFrame`s with zero GA logic in JS/Swift.
-/

namespace Grassmann.CoffeeShop

open Grassmann.Scene Grassmann.Eval

/-- Mutable state of the CoffeeShop & Surface studio workspace. -/
structure CoffeeShopState where
  presetId       : String := "pga3d_slicing"
  customAlgebra  : String := "PGA3"
  customCode     : String := ""
  useCustom      : Bool   := false
  surfaceExpr    : String := "0.55 * sin(1.8*x + t) * cos(1.8*y)"
  surfaceBounds  : Float × Float × Float × Float := (-2.0, 2.0, -2.0, 2.0)
  surfaceGridN   : Nat    := 40
  useSurface     : Bool   := false
  eqOverlay      : Option ContourOverlay := none
  handles        : Array (UInt32 × Vec3) := #[]
  coeffOverrides : Array (UInt32 × UInt32 × Float) := #[]
  sliceMotor     : Option Motor3 := none
  customCamera   : Option CameraState := none
  simTime        : Float := 0.0
  -- Persistent RK4 physics state for `pga3d_physics_free_top`
  topMotor       : Motor3 := Motor3.identity
  topOmega       : Vec3   := ⟨0.08, 3.2, 0.05⟩ -- Perturbed intermediate axis => Dzhanibekov flip!
  topTrail       : FloatArray := FloatArray.empty
  deriving Inhabited

def CoffeeShopState.init (presetId : String := "pga3d_slicing") : CoffeeShopState :=
  { presetId }

def loadPreset (st : CoffeeShopState) (presetId : String) : CoffeeShopState :=
  { st with
    presetId,
    useCustom := false,
    useSurface := false,
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

/-- Live coefficient edit from CoffeeShop's `inspect stash` table: records override and
maps blade edits directly onto interactive handles (`0..2` → `x/y/z`) or `#pga3d_slicing` plane! -/
def setCoeffOverride (st : CoffeeShopState) (entryIdx bladeIdx : UInt32) (val : Float) :
    CoffeeShopState :=
  let nextOv :=
    match st.coeffOverrides.findIdx? fun x => x.1 == entryIdx && x.2.1 == bladeIdx with
    | some idx => st.coeffOverrides.set! idx (entryIdx, bladeIdx, val)
    | none     => st.coeffOverrides.push (entryIdx, bladeIdx, val)
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
  { st with customAlgebra := algebra, customCode := code, useCustom := true, useSurface := false }

def setSurface (st : CoffeeShopState) (expr : String)
    (minX maxX minY maxY : Float) (gridN : Nat) : CoffeeShopState :=
  { st with
    surfaceExpr := expr,
    surfaceBounds := (minX, maxX, minY, maxY),
    surfaceGridN := max 8 (min 96 gridN),
    useSurface := true,
    useCustom := false }

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
  if st.presetId == "pga3d_physics_free_top" && !st.useCustom && !st.useSurface then
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

/-- Emit the live `SceneFrame` for the active CoffeeShop preset, custom script, or 3D surface. -/
def toSceneFrame (st : CoffeeShopState) (frameSeq : UInt64 := 0) : SceneFrame :=
  let f0 : SceneFrame :=
    if st.useSurface then
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
      evalScriptToFrame st.customAlgebra st.customCode st.handles st.simTime frameSeq
    else
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
      | _                          => buildPga3dSlicing st.handles st.sliceMotor frameSeq st.simTime
  let f1 := match st.customCamera with
    | some cam => { f0 with camera := cam }
    | none     => f0
  match st.eqOverlay with
  | some ov => { f1 with contourOverlay := some ov }
  | none    => f1

end Grassmann.CoffeeShop
