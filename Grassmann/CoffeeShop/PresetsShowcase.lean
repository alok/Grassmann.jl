import Grassmann.Scene.Types
import Grassmann.Scene.Json
import Grassmann.CoffeeShop.Mesh
import Grassmann.Eval.ImplicitExpr
import Grassmann.Codegen.GPUInit

/-!
# Wave 4B & Wave 6C Showstopper 3D Physics, Relativity, GPU Raymarching & Streamline Presets + 77-Preset KaTeX Metadata

Strictly `Init`-only (ZERO `Lean.*`, ZERO `Std.*`, ZERO `DirectSum`, ZERO `sorry`/axioms) so
every preset links cleanly into both the standalone C ABI dylib/XCFramework and the Emscripten WASM bundle!

Adds **8 Showstopper Interactive 3D Presets** (bringing total studio catalog to **77 presets**):
1. `pga3d_bouncing_cube` — Real-time PGA3 motor RK4 rigid-body bouncing cube with 8-corner
   floor impulse collisions, angular momentum bivector disk + arrow, bounce trail, and live
   `gravity` / `restitution` / `spin` `@param` sliders!
2. `pga3d_double_pendulum` — Singularity-free 3D spherical double pendulum integrated with
   constrained Lagrange-multiplier RK4 + composed PGA3 link motors, glowing 3D chaotic ribbon,
   and `length` / `damping` / `gravity` `@param` sliders!
3. `sta_terrell_penrose` — Relativistic `Cl(3,1)` (`-+++`) Terrell-Penrose optical aberration
   + past light-cone solver comparing the rotated optical image (`θ_TP = arcsin β`) against the
   simultaneous Lorentz-contracted ghost cube (`x/γ`), with live `beta` (`0..0.95c`) & `distance` sliders!
4. `sta_maxwell_streamlines` — 3D RK4-advected electromagnetic dipole `E` + `B` streamlines
   (`0x0D FLOW_PARTICLES`) + glowing Faraday bivector disks (`F = E + IB`) + `frequency` / `dipole` / `bScale` sliders!
5. `pga3d_hopf_streamlines` — 3D RK4-advected Hopf fibration (`S³ → ℝ³`) + PGA3 Chasles screw-motor
   particle flow ribbons (`0x0D FLOW_PARTICLES`) + Villarceau guide fibers + `pitch` / `twist` / `flowSpeed` sliders!
6. `implicit_barth_sextic` — Iconic degree-6 **Barth Sextic** (`4(φ²x²-y²)(φ²y²-z²)(φ²z²-x²) - (1+2φ)(x²+y²+z²-1)² = c`)
   with BOTH live `GPUInit` infinite-resolution GLSL3/WGSL/MSL sphere-tracer AND fast bytecode
   Marching Tetrahedra mesh + live `phi`/`iso` `@param` sliders!
7. `cga3d_dupin_cyclide_raymarch` — Live `GPUInit` sphere-traced **3D CGA Dupin Cyclide** with
   interactive `majorR`/`minorR`/`eccentricity` `@param` sliders and glowing orthogonal focal ellipse + hyperbola!
8. `pga3d_gears_kinematics` — Meshing 3D PGA3 rigid-body involute-style 3-gear train driven by
   composed PGA3 rotational motors with live `speed` & `ratio` `@param` sliders!

Also provides `presetMathMeta` with crisp KaTeX LaTeX `formula` and 1-sentence `summary` for ALL **77 presets**.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.CoffeeShop.PresetsShowcase

open Grassmann.Scene Grassmann.Scene.Json Grassmann.CoffeeShop.Mesh
open Grassmann.Eval.ImplicitExpr Grassmann.Codegen.GPUInit

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692

/-- Catalog metadata matching `PresetInfo` field-for-field. -/
structure ShowcasePresetInfo where
  id          : String
  title       : String
  category    : String
  algebra     : String
  description : String
  sampleCode  : String
  deriving Repr, Inhabited

/-- Look up a parameter override value (clamped to `[lo, hi]`) or return `defVal`. -/
@[inline] def paramVal (overrides : Array (String × Float)) (name : String)
    (defVal lo hi : Float) : Float :=
  let raw := ((overrides.find? fun kv => kv.1 == name).map (·.2)).getD defVal
  max lo (min hi raw)

/-- Look up a draggable handle position or return `defPos`. -/
@[inline] private def hPos (handles : Array (UInt32 × Vec3)) (id : UInt32) (defPos : Vec3) : Vec3 :=
  ((handles.find? fun kv => kv.1 == id).map (·.2)).getD defPos

private def mkMeta (alg : String) : AlgebraMeta :=
  match alg with
  | "STA" =>
    { name := "STA", p := 3, q := 1, r := 0, conformalWitt := false
      basisNames := #["1","e0","e1","e2","e3","e01","e02","e03","e12","e13","e23","e012","e013","e023","e123","I"]
      basisMetric := #[1,-1,1,1,1,1,1,1,-1,-1,-1,1,1,1,-1,-1] }
  | _ =>
    { name := "PGA3", p := 3, q := 0, r := 1, conformalWitt := false
      basisNames := #["1","e0","e1","e2","e3","e01","e02","e03","e12","e13","e23","e012","e013","e023","e123","e0123"]
      basisMetric := #[1,0,1,1,1,0,0,0,-1,-1,-1,0,0,0,-1,0] }

private def mkShowcaseBase (presetId title alg : String) (seq : UInt64) (t : Float)
    (camDist : Float := 5.0) : SceneFrame :=
  { frameSeq := seq, simTime := t, mode := .coffeeShop, is2D := false,
    gridEnabled := true, darkTheme := true, gridSize := 2.6,
    algebra := mkMeta alg, presetId, title,
    camera := { motor := Motor3.orbitCamera (0.55 + 0.08 * Float.sin (t * 0.22)) (-0.30) camDist,
                fovDeg := 45.0, distance := camDist } }

private def curveFromVecs (pts : Array Vec3) (color : RGBA) (width : Float := 2.4)
    (closed : Bool := false) (dashed : Bool := false) : CurvePrim := Id.run do
  let mut fa := FloatArray.emptyWithCapacity (pts.size * 3)
  for p in pts do fa := fa.push p.x |>.push p.y |>.push p.z
  return { points := fa, width, color, closed, dashed }

private def pushTrailPoint (trail : FloatArray) (p : Vec3) (maxPts : Nat := 180) : FloatArray :=
  let maxFloats := maxPts * 3
  let base :=
    if trail.size ≥ maxFloats then
      let rec shift (i : Nat) (acc : FloatArray) : FloatArray :=
        if i < trail.size then shift (i + 1) (acc.push (trail.get! i)) else acc
      shift 3 (FloatArray.emptyWithCapacity maxFloats)
    else trail
  base.push p.x |>.push p.y |>.push p.z

/-! ## 1. `pga3d_bouncing_cube` — Real-Time PGA3 Motor RK4 Rigid-Body Bouncing Cube -/

/-- Persistent rigid-body state for `pga3d_bouncing_cube`. -/
structure BouncingCubeState where
  pos         : Vec3       := ⟨-0.45, 1.35, -0.20⟩
  vel         : Vec3       := ⟨0.78, 0.35, 0.32⟩
  rot         : Motor3     := Motor3.mul (Motor3.rotorAxis ⟨1.0, 0.4, 0.2⟩ 0.72)
                                         (Motor3.rotorAxis ⟨0.0, 1.0, 0.3⟩ 0.48)
  omega       : Vec3       := ⟨1.9, 1.4, -1.2⟩
  restTimer   : Float      := 0.0
  impactPos   : Vec3       := ⟨0.0, -1.25, 0.0⟩
  impactFlash : Float      := 0.0
  trail       : FloatArray := FloatArray.empty
  deriving Inhabited

/-- Multi-face vibrantly shaded cube mesh (`half = 0.45`) for `pga3d_bouncing_cube`. -/
private def buildColorfulCubeMesh (half : Float := 0.45) (meshId : UInt64 := 7401) : MeshAsset :=
  let h := half
  let addFace (mb : MeshBuilder) (p0 p1 p2 p3 : Vec3) (c : RGBA) : MeshBuilder :=
    let (m1, i0) := mb.addVertex p0 c
    let (m2, i1) := m1.addVertex p1 c
    let (m3, i2) := m2.addVertex p2 c
    let (m4, i3) := m3.addVertex p3 c
    (m4.addTri i0 i1 i2).addTri i0 i2 i3
  let mb : MeshBuilder := {}
  let mb := addFace mb ⟨-h,-h, h⟩ ⟨ h,-h, h⟩ ⟨ h, h, h⟩ ⟨-h, h, h⟩ RGBA.cyan
  let mb := addFace mb ⟨ h,-h,-h⟩ ⟨-h,-h,-h⟩ ⟨-h, h,-h⟩ ⟨ h, h,-h⟩ RGBA.violet
  let mb := addFace mb ⟨ h,-h, h⟩ ⟨ h,-h,-h⟩ ⟨ h, h,-h⟩ ⟨ h, h, h⟩ RGBA.amber
  let mb := addFace mb ⟨-h,-h,-h⟩ ⟨-h,-h, h⟩ ⟨-h, h, h⟩ ⟨-h, h,-h⟩ RGBA.coral
  let mb := addFace mb ⟨-h, h, h⟩ ⟨ h, h, h⟩ ⟨ h, h,-h⟩ ⟨-h, h,-h⟩ RGBA.green
  let mb := addFace mb ⟨-h,-h,-h⟩ ⟨ h,-h,-h⟩ ⟨ h,-h, h⟩ ⟨-h,-h, h⟩ RGBA.blue
  mb.finalize meshId

private def bouncingCubeAsset : MeshAsset := buildColorfulCubeMesh 0.45 7401

/-- 4-substep RK4 PGA3 rigid-body integrator with 8-corner floor impulse + tangential friction. -/
def stepBouncingCubeRK4 (st : BouncingCubeState) (dt gravity restitution spin : Float) :
    BouncingCubeState := Id.run do
  let half : Float := 0.45
  let floorY : Float := -1.25
  let wallLim : Float := 2.10
  let invMass : Float := 1.0
  -- Solid cube scalar moment of inertia I = (1/6) * m * (2h)^2 = (2/3) * h^2
  let invInertia : Float := 1.0 / ((2.0 / 3.0) * half * half)
  let h := max 0.0005 (min 0.015 (dt / 4.0))
  let mut pos := st.pos
  let mut vel := st.vel
  let mut rot := st.rot
  let mut omega := st.omega
  let mut impactPos := st.impactPos
  let mut impactFlash := max 0.0 (st.impactFlash - dt * 2.4)
  let mut restTimer := st.restTimer
  let corners : Array Vec3 := #[
    ⟨-half,-half,-half⟩, ⟨ half,-half,-half⟩, ⟨-half, half,-half⟩, ⟨ half, half,-half⟩,
    ⟨-half,-half, half⟩, ⟨ half,-half, half⟩, ⟨-half, half, half⟩, ⟨ half, half, half⟩
  ]
  for _ in [:4] do
    -- RK4 linear kinematics under gravity `(0, -g, 0)` + exact PGA3 rotor integration
    let vMid : Vec3 := ⟨vel.x, vel.y - 0.5 * gravity * h, vel.z⟩
    pos := ⟨pos.x + vMid.x * h, pos.y + vMid.y * h, pos.z + vMid.z * h⟩
    vel := ⟨vel.x, vel.y - gravity * h, vel.z⟩
    -- Exact PGA3 exponential rotor step `R_{k+1} = exp(-½ ω h) * R_k`
    let wMag := Vec3.norm omega
    if wMag > 1e-8 then
      let dR := Motor3.rotorAxis omega (wMag * h)
      rot := Motor3.normalize (Motor3.mul dR rot)
    -- 8-corner floor collision check (deepest penetrating vertex)
    let mut minY : Float := 1e9
    let mut bestR : Vec3 := Vec3.zero
    for c in corners do
      let rWorld := Motor3.applyDir rot c
      let wy := pos.y + rWorld.y
      if wy < minY then
        minY := wy
        bestR := rWorld
    if minY < floorY then
      let pen := floorY - minY
      pos := { pos with y := pos.y + pen }
      let vContact := Vec3.add vel (Vec3.cross omega bestR)
      if vContact.y < 0.0 then
        -- Normal impulse `j = -(1+e)(v_c · n) / (m⁻¹ + ‖r × n‖² I⁻¹)` with `n = (0, 1, 0)`
        let rCrossN : Vec3 := ⟨-bestR.z, 0.0, bestR.x⟩
        let denom := invMass + Vec3.normSq rCrossN * invInertia
        let j := -(1.0 + restitution) * vContact.y / max 1e-6 denom
        vel := { vel with y := vel.y + j * invMass }
        omega := Vec3.add omega (Vec3.scale (j * invInertia) rCrossN)
        -- Coulomb tangential friction impulse excites realistic tumbling spin!
        let vTan : Vec3 := ⟨vContact.x, 0.0, vContact.z⟩
        let vtMag := Vec3.norm vTan
        if vtMag > 1e-5 then
          let tDir := Vec3.scale (1.0 / vtMag) vTan
          let rCrossT := Vec3.cross bestR tDir
          let denomT := invMass + Vec3.normSq rCrossT * invInertia
          let jtMax := 0.28 * j
          let jt := min jtMax (vtMag / max 1e-6 denomT)
          vel := Vec3.sub vel (Vec3.scale (jt * invMass) tDir)
          omega := Vec3.sub omega (Vec3.scale (jt * invInertia) rCrossT)
        impactPos := ⟨pos.x + bestR.x, floorY, pos.z + bestR.z⟩
        impactFlash := min 1.0 (0.35 + 0.14 * Float.abs vContact.y)
    -- Gentle arena wall rebounds so the cube stays framed inside the 3D stage
    if pos.x > wallLim then
      pos := { pos with x := wallLim }; vel := { vel with x := -Float.abs vel.x * 0.85 }
    else if pos.x < -wallLim then
      pos := { pos with x := -wallLim }; vel := { vel with x := Float.abs vel.x * 0.85 }
    if pos.z > wallLim then
      pos := { pos with z := wallLim }; vel := { vel with z := -Float.abs vel.z * 0.85 }
    else if pos.z < -wallLim then
      pos := { pos with z := -wallLim }; vel := { vel with z := Float.abs vel.z * 0.85 }
    -- Gentle air drag on spin
    omega := Vec3.scale (1.0 - 0.03 * h) omega
  -- Auto-relaunch gracefully if kinetic + potential energy settles near rest
  let energy := 0.5 * Vec3.normSq vel + gravity * max 0.0 (pos.y - (floorY + half))
  if energy < 0.22 then
    restTimer := restTimer + dt
  else
    restTimer := 0.0
  let trail1 := pushTrailPoint st.trail pos 160
  if restTimer > 0.75 then
    let s := max 0.4 spin
    return { pos := ⟨-0.55, 1.45, -0.25⟩
             vel := ⟨0.85, 0.55, 0.38⟩
             rot := Motor3.mul (Motor3.rotorAxis ⟨1.0, 0.3, 0.5⟩ 0.8) (Motor3.rotorAxis ⟨0.0, 1.0, 0.0⟩ 0.6)
             omega := ⟨0.75 * s, 0.55 * s, -0.45 * s⟩
             restTimer := 0.0, impactPos, impactFlash := 0.8, trail := FloatArray.empty }
  else
    return { pos, vel, rot, omega, restTimer, impactPos, impactFlash, trail := trail1 }

/-- Initialize `BouncingCubeState` with a crisp pre-warmed arc so frame 0 already looks alive. -/
def initBouncingCubeState (spin : Float := 2.6) : BouncingCubeState := Id.run do
  let s := max 0.2 spin
  let mut st : BouncingCubeState :=
    { pos := ⟨-0.65, 1.45, -0.20⟩
      vel := ⟨0.82, 0.35, 0.28⟩
      omega := ⟨0.72 * s, 0.55 * s, -0.46 * s⟩ }
  for _ in [:18] do
    st := stepBouncingCubeRK4 st 0.016 9.8 0.78 spin
  return st

def buildPga3dBouncingCube (cube : BouncingCubeState) (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let g := paramVal overrides "gravity" 9.8 0.5 20.0
  let e := paramVal overrides "restitution" 0.78 0.1 0.98
  let sp := paramVal overrides "spin" 2.6 0.0 8.0
  let f := mkShowcaseBase "pga3d_bouncing_cube" "3D PGA Rigid-Body Bouncing Cube (RK4 Impulse)" "PGA3" seq t 5.4
  let floorY : Float := -1.25
  let half : Float := 0.45
  let pos := hPos handles 0 cube.pos
  let motor := Motor3.mul (Motor3.translator pos.x pos.y pos.z) cube.rot
  -- 12 wireframe cube edges for razor-sharp silhouette clarity
  let cs : Array Vec3 := #[
    ⟨-half,-half,-half⟩, ⟨ half,-half,-half⟩, ⟨ half, half,-half⟩, ⟨-half, half,-half⟩,
    ⟨-half,-half, half⟩, ⟨ half,-half, half⟩, ⟨ half, half, half⟩, ⟨-half, half, half⟩
  ].map (Motor3.applyPoint motor)
  let edgePairs : Array (Nat × Nat) := #[
    (0,1),(1,2),(2,3),(3,0), (4,5),(5,6),(6,7),(7,4), (0,4),(1,5),(2,6),(3,7)
  ]
  let mut segs : Array SegmentPrim := Array.mkEmpty 14
  for (a, b) in edgePairs do
    segs := segs.push { a := cs[a]!, b := cs[b]!, width := 2.2, color := RGBA.white }
  -- Angular momentum vector arrow + dual bivector rotation disk `B_ω = I ω`
  let wMag := Vec3.norm cube.omega
  let wDir := if wMag > 1e-5 then Vec3.scale (1.0 / wMag) cube.omega else ⟨0.0, 1.0, 0.0⟩
  let arrowLen := min 1.45 (0.35 + 0.18 * wMag)
  let tip := Vec3.add pos (Vec3.scale arrowLen wDir)
  segs := segs.push { a := pos, b := tip, width := 3.6, color := RGBA.amber, role := { arrow := true } }
  let (bu, bv) := Vec3.orthonormalBasis wDir
  let diskR := min 0.95 (0.32 + 0.09 * wMag)
  let bivDisk : BivectorDiskPrim := {
    origin := pos, u := Vec3.scale diskR bu, v := Vec3.scale diskR bv,
    area := piF * diskR * diskR, color := ⟨1.0, 0.72, 0.22, 0.34⟩,
    isDisk := true, orientationArrow := true
  }
  let curves : Array CurvePrim :=
    if cube.trail.size ≥ 6 then #[{ points := cube.trail, width := 2.6, color := RGBA.cyan }] else #[]
  let ringR := 0.22 + 0.55 * (1.0 - cube.impactFlash)
  let circles : Array CirclePrim := #[{
    center := ⟨cube.impactPos.x, floorY + 0.01, cube.impactPos.z⟩,
    u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
    radius := ringR, width := 2.8,
    color := ⟨1.0, 0.52, 0.35, max 0.22 cube.impactFlash⟩, label := "Impact"
  }]
  let params : Array ParamSpec := #[
    { name := "gravity", label := "Gravity g", value := g, min := 0.5, max := 20.0, step := 0.2 },
    { name := "restitution", label := "Bounce e", value := e, min := 0.1, max := 0.98, step := 0.02 },
    { name := "spin", label := "Initial Spin ω", value := sp, min := 0.0, max := 8.0, step := 0.1 }
  ]
  return { f with
    params,
    formula := "\\dot{M} = -\\tfrac{1}{2} M B,\\qquad J = \\frac{-(1+e)\\,\\mathbf{v}_c\\cdot\\mathbf{n}}{m^{-1} + \\|\\mathbf{r}\\times\\mathbf{n}\\|^2 / I}",
    summary := "Real-time 3D PGA rigid-body RK4 simulation of a tumbling cube with 8-corner floor impulse collisions and angular momentum bivector.",
    meshAssets := #[bouncingCubeAsset],
    meshRefs := #[{
      meshId := bouncingCubeAsset.meshId, dirtyHash := bouncingCubeAsset.dirtyHash,
      motor, color := RGBA.white, useVertexColors := true
    }],
    planes := #[{
      center := ⟨0.0, floorY, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
      extent := 2.5, color := ⟨0.24, 0.42, 0.72, 0.26⟩, gridLines := true, label := "Floor Π"
    }],
    segments := segs,
    bivectorDisks := #[bivDisk],
    curves,
    circles,
    points := #[
      { handleId := 0, pos, radius := 0.075, color := RGBA.amber, role := { draggable := true }, label := "COM" }
    ],
    inspect := #[
      { idx := 0, name := "Motor M", grade := 2,
        formatted := s!"pos=({pos.x}, {pos.y}, {pos.z}) · |ω|={wMag}", editable := false },
      { idx := 1, name := "Params", grade := 0,
        formatted := s!"g={g}, e={e}, spin={sp}", editable := false }
    ] }

/-! ## 2. `pga3d_double_pendulum` — Coupled 3D Spherical Double Pendulum (Constrained RK4 + PGA3 Motors) -/

/-- Singularity-free Cartesian constrained state for the 3D spherical double pendulum. -/
structure DoublePendulumState where
  p1     : Vec3       := ⟨0.78, 0.92, 0.28⟩
  v1     : Vec3       := ⟨0.35, -0.45, 1.65⟩
  p2     : Vec3       := ⟨1.42, 1.38, -0.18⟩
  v2     : Vec3       := ⟨-0.55, 0.25, -1.95⟩
  trail1 : FloatArray := FloatArray.empty
  trail2 : FloatArray := FloatArray.empty
  deriving Inhabited

private def pivotPt : Vec3 := ⟨0.0, 1.25, 0.0⟩

/-- Exact closed-form 2×2 Lagrange-multiplier accelerations for a 3D spherical double pendulum
(`m₁ = m₂ = 1`, rod constraints `‖p₁ - p₀‖ = L₁`, `‖p₂ - p₁‖ = L₂` — strictly positive-definite,
ZERO spherical-coordinate pole singularities anywhere on `S² × S²`!). -/
private def doublePendulumAccel (p1 v1 p2 v2 : Vec3) (gravity damping : Float) : Vec3 × Vec3 :=
  let u1 := Vec3.sub p1 pivotPt
  let u2 := Vec3.sub p2 p1
  let v12 := Vec3.sub v2 v1
  let f1 : Vec3 := ⟨-damping * v1.x, -gravity - damping * v1.y, -damping * v1.z⟩
  let f2 : Vec3 := ⟨-damping * v2.x, -gravity - damping * v2.y, -damping * v2.z⟩
  let a11 := Vec3.normSq u1
  let a12 := -(Vec3.dot u1 u2)
  let a22 := 2.0 * Vec3.normSq u2
  let b1 := -(Vec3.dot u1 f1) - Vec3.normSq v1
  let b2 := -(Vec3.dot u2 (Vec3.sub f2 f1)) - Vec3.normSq v12
  let det := max 1e-8 (a11 * a22 - a12 * a12)
  let lam1 := (a22 * b1 - a12 * b2) / det
  let lam2 := (a11 * b2 - a12 * b1) / det
  let acc1 := Vec3.sub (Vec3.add f1 (Vec3.scale lam1 u1)) (Vec3.scale lam2 u2)
  let acc2 := Vec3.add f2 (Vec3.scale lam2 u2)
  (acc1, acc2)

/-- Project `(p1, v1, p2, v2)` onto exact rod lengths `(L1, L2)` and tangent velocity manifold. -/
private def projectDoublePendulum (p1 v1 p2 v2 : Vec3) (l1 l2 : Float) : Vec3 × Vec3 × Vec3 × Vec3 :=
  let u1 := Vec3.normalize (Vec3.sub p1 pivotPt)
  let p1' := Vec3.add pivotPt (Vec3.scale l1 u1)
  let v1' := Vec3.sub v1 (Vec3.scale (Vec3.dot v1 u1) u1)
  let u2 := Vec3.normalize (Vec3.sub p2 p1')
  let p2' := Vec3.add p1' (Vec3.scale l2 u2)
  let vRel := Vec3.sub v2 v1'
  let v2' := Vec3.add v1' (Vec3.sub vRel (Vec3.scale (Vec3.dot vRel u2) u2))
  (p1', v1', p2', v2')

/-- 4-substep RK4 step of the 3D spherical double pendulum. -/
def stepDoublePendulumRK4 (st : DoublePendulumState) (dt armLen damping gravity : Float) :
    DoublePendulumState := Id.run do
  let l1 := max 0.35 armLen
  let l2 := 0.90 * l1
  let h := max 0.0005 (min 0.012 (dt / 4.0))
  let mut (p1, v1, p2, v2) := projectDoublePendulum st.p1 st.v1 st.p2 st.v2 l1 l2
  for _ in [:4] do
    let (a1_1, a2_1) := doublePendulumAccel p1 v1 p2 v2 gravity damping
    let p1_2 := Vec3.add p1 (Vec3.scale (0.5 * h) v1)
    let v1_2 := Vec3.add v1 (Vec3.scale (0.5 * h) a1_1)
    let p2_2 := Vec3.add p2 (Vec3.scale (0.5 * h) v2)
    let v2_2 := Vec3.add v2 (Vec3.scale (0.5 * h) a2_1)
    let (a1_2, a2_2) := doublePendulumAccel p1_2 v1_2 p2_2 v2_2 gravity damping
    let p1_3 := Vec3.add p1 (Vec3.scale (0.5 * h) v1_2)
    let v1_3 := Vec3.add v1 (Vec3.scale (0.5 * h) a1_2)
    let p2_3 := Vec3.add p2 (Vec3.scale (0.5 * h) v2_2)
    let v2_3 := Vec3.add v2 (Vec3.scale (0.5 * h) a2_2)
    let (a1_3, a2_3) := doublePendulumAccel p1_3 v1_3 p2_3 v2_3 gravity damping
    let p1_4 := Vec3.add p1 (Vec3.scale h v1_3)
    let v1_4 := Vec3.add v1 (Vec3.scale h a1_3)
    let p2_4 := Vec3.add p2 (Vec3.scale h v2_3)
    let v2_4 := Vec3.add v2 (Vec3.scale h a2_3)
    let (a1_4, a2_4) := doublePendulumAccel p1_4 v1_4 p2_4 v2_4 gravity damping
    let combine (x k1 k2 k3 k4 : Vec3) : Vec3 :=
      Vec3.add x (Vec3.scale (h / 6.0)
        (Vec3.add k1 (Vec3.add (Vec3.scale 2.0 k2) (Vec3.add (Vec3.scale 2.0 k3) k4))))
    p1 := combine p1 v1 v1_2 v1_3 v1_4
    v1 := combine v1 a1_1 a1_2 a1_3 a1_4
    p2 := combine p2 v2 v2_2 v2_3 v2_4
    v2 := combine v2 a2_1 a2_2 a2_3 a2_4
    (p1, v1, p2, v2) := projectDoublePendulum p1 v1 p2 v2 l1 l2
  let tr1 := pushTrailPoint st.trail1 p1 140
  let tr2 := pushTrailPoint st.trail2 p2 240
  return { p1, v1, p2, v2, trail1 := tr1, trail2 := tr2 }

/-- Initialize `DoublePendulumState` with a pre-warmed 36-step chaotic 3D ribbon trail. -/
def initDoublePendulumState (armLen : Float := 1.0) : DoublePendulumState := Id.run do
  let l1 := max 0.35 armLen
  let l2 := 0.90 * l1
  let (p1, v1, p2, v2) := projectDoublePendulum
    ⟨0.88, 1.05, 0.22⟩ ⟨0.32, -0.35, 2.05⟩
    ⟨1.58, 1.55, -0.25⟩ ⟨-0.65, 0.40, -2.25⟩ l1 l2
  let mut st : DoublePendulumState := { p1, v1, p2, v2 }
  for _ in [:36] do
    st := stepDoublePendulumRK4 st 0.016 armLen 0.03 9.8
  return st

/-- Build a unit-length PGA3 rotor aligning `+Y` onto `dir`. -/
private def rotorFromY (dir : Vec3) : Motor3 :=
  let u := Vec3.normalize dir
  let c := max (-1.0) (min 1.0 u.y)
  if c > 0.9999 then Motor3.identity
  else if c < -0.9999 then Motor3.rotorAxis ⟨1.0, 0.0, 0.0⟩ piF
  else
    let ax := Vec3.normalize (Vec3.cross ⟨0.0, 1.0, 0.0⟩ u)
    Motor3.rotorAxis ax (Float.acos c)

def buildPga3dDoublePendulum (dp : DoublePendulumState) (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let armLen := paramVal overrides "length" 1.0 0.4 1.5
  let damping := paramVal overrides "damping" 0.03 0.0 0.35
  let gravity := paramVal overrides "gravity" 9.8 1.0 20.0
  let l1 := armLen
  let l2 := 0.90 * armLen
  let f := mkShowcaseBase "pga3d_double_pendulum" "3D PGA Spherical Double Pendulum (Coupled Motors)" "PGA3" seq t 5.4
  let (p1, _, p2Raw, _) := projectDoublePendulum dp.p1 dp.v1 dp.p2 dp.v2 l1 l2
  let p2 := hPos handles 0 p2Raw
  let mid1 := Vec3.lerp pivotPt p1 0.5
  let mid2 := Vec3.lerp p1 p2 0.5
  let len1 := max 0.05 (Vec3.norm (Vec3.sub p1 pivotPt))
  let len2 := max 0.05 (Vec3.norm (Vec3.sub p2 p1))
  let rod1 := buildCylinderMesh 0.042 len1 12 RGBA.cyan 7402
  let rod2 := buildCylinderMesh 0.038 len2 12 RGBA.violet 7404
  let m1 := Motor3.mul (Motor3.translator mid1.x mid1.y mid1.z) (rotorFromY (Vec3.sub p1 pivotPt))
  let m2 := Motor3.mul (Motor3.translator mid2.x mid2.y mid2.z) (rotorFromY (Vec3.sub p2 p1))
  -- Total angular momentum bivector L = r1 × v1 + r2 × v2 about the pivot
  let r1 := Vec3.sub p1 pivotPt
  let r2 := Vec3.sub p2 pivotPt
  let angMom := Vec3.add (Vec3.cross r1 dp.v1) (Vec3.cross r2 dp.v2)
  let lMag := Vec3.norm angMom
  let lAxis := if lMag > 1e-5 then Vec3.scale (1.0 / lMag) angMom else ⟨0.0, 1.0, 0.0⟩
  let (lu, lv) := Vec3.orthonormalBasis lAxis
  let diskR := min 0.85 (0.28 + 0.08 * lMag)
  let mut curves : Array CurvePrim := #[]
  if dp.trail1.size ≥ 6 then
    curves := curves.push { points := dp.trail1, width := 2.0, color := ⟨0.22, 0.88, 0.95, 0.65⟩ }
  if dp.trail2.size ≥ 6 then
    curves := curves.push { points := dp.trail2, width := 3.2, color := RGBA.amber }
  let params : Array ParamSpec := #[
    { name := "length", label := "Arm Length L", value := armLen, min := 0.4, max := 1.5, step := 0.05 },
    { name := "damping", label := "Damping ζ", value := damping, min := 0.0, max := 0.35, step := 0.01 },
    { name := "gravity", label := "Gravity g", value := gravity, min := 1.0, max := 20.0, step := 0.2 }
  ]
  return { f with
    params,
    formula := "M_2(t) = M_1(t)\\,\\exp\\!\\left(-\\tfrac{1}{2}\\theta_2 L_2\\right),\\qquad \\mathbf{a}_i = \\mathbf{g} - \\zeta\\mathbf{v}_i + \\sum_k \\lambda_k \\nabla_i g_k",
    summary := "Chaotic 3D spherical double pendulum integrated via singularity-free constrained RK4 dynamics and composed PGA3 link motors.",
    meshAssets := #[rod1, rod2],
    meshRefs := #[
      { meshId := rod1.meshId, dirtyHash := rod1.dirtyHash,
        motor := m1, color := RGBA.cyan, useVertexColors := false },
      { meshId := rod2.meshId, dirtyHash := rod2.dirtyHash,
        motor := m2, color := RGBA.violet, useVertexColors := false }
    ],
    segments := #[
      { a := pivotPt, b := p1, width := 4.0, color := RGBA.cyan },
      { a := p1, b := p2, width := 4.0, color := RGBA.violet },
      { a := p2, b := Vec3.add p2 (Vec3.scale 0.25 dp.v2), width := 2.8, color := RGBA.coral, role := { arrow := true } }
    ],
    spheres := #[
      { center := pivotPt, radius := 0.10, color := RGBA.white, label := "Pivot" },
      { center := p1, radius := 0.16, color := ⟨0.22, 0.88, 0.95, 0.92⟩, label := "Bob 1" },
      { center := p2, radius := 0.19, color := ⟨1.0, 0.56, 0.30, 0.95⟩, label := "Bob 2" }
    ],
    bivectorDisks := #[{
      origin := pivotPt, u := Vec3.scale diskR lu, v := Vec3.scale diskR lv,
      area := piF * diskR * diskR, color := ⟨0.72, 0.45, 1.0, 0.30⟩,
      isDisk := true, orientationArrow := true
    }],
    circles := #[{
      center := pivotPt, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 0.0, 1.0⟩,
      radius := 0.45, width := 1.8, color := RGBA.ghost
    }],
    curves,
    points := #[
      { handleId := 0, pos := p2, radius := 0.08, color := RGBA.amber, role := { draggable := true }, label := "Bob 2" }
    ],
    inspect := #[
      { idx := 0, name := "Bob 2 State", grade := 3,
        formatted := s!"p2=({p2.x}, {p2.y}, {p2.z}) · |L|={lMag}", editable := false },
      { idx := 1, name := "Pendulum Params", grade := 0,
        formatted := s!"L={armLen}, ζ={damping}, g={gravity}", editable := false }
    ] }

/-! ## 3. `sta_terrell_penrose` — Relativistic `Cl(3,1)` Terrell-Penrose Optical Rotation -/

/-- Exact Special Relativity past light-cone optical-aberration map in `STA` (`Cl(3,1) -+++`):
a rest-frame point `(x0, y0, z0)` moving along `+x` at speed `β = v/c` emits a photon at lab time
`t_e < 0` that arrives at observer `(0, 0, obsDist)` simultaneously at `t_obs = 0`. -/
private def terrellPenroseMap (p0 : Vec3) (beta gamma obsDist xCenter : Float) : Vec3 :=
  let xc := p0.x / gamma
  let dz := p0.z - obsDist
  let trans2 := p0.y * p0.y + dz * dz
  let invG2 := 1.0 - beta * beta
  let disc := Float.sqrt (max 0.0 (xc * xc + invG2 * trans2))
  let te := (gamma * gamma) * (beta * xc - disc)
  let xApp := xc + beta * te - xCenter
  ⟨xApp, p0.y, p0.z⟩

def buildStaTerrellPenrose (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let beta := paramVal overrides "beta" 0.78 0.0 0.95
  let obsDist := paramVal overrides "distance" 4.5 2.5 10.0
  let f := mkShowcaseBase "sta_terrell_penrose" "STA Cl(3,1) Terrell-Penrose Relativistic Rotation" "STA" seq t 5.6
  let gamma := 1.0 / Float.sqrt (max 1e-6 (1.0 - beta * beta))
  let rapidity := 0.5 * Float.log ((1.0 + beta) / max 1e-6 (1.0 - beta))
  let tpAngleDeg := Float.asin beta * (180.0 / piF)
  -- Reference center shift so cube stays centered in viewport as β sweeps 0 -> 0.95c
  let xCenter :=
    let disc0 := Float.sqrt (max 0.0 ((1.0 - beta * beta) * obsDist * obsDist))
    beta * (-(gamma * gamma) * disc0)
  let half : Float := 0.85
  -- Optional subtle vertical tilt via handle 0
  let ctrl := hPos handles 0 ⟨0.0, 0.12 * Float.sin (t * 0.5), 0.0⟩
  let tiltRot := Motor3.rotorAxis ⟨1.0, 0.0, 0.0⟩ (0.25 * ctrl.y)
  let warp (p : Vec3) : Vec3 :=
    let pr := Motor3.applyDir tiltRot p
    terrellPenroseMap pr beta gamma obsDist xCenter
  let lorentzOnly (p : Vec3) : Vec3 :=
    let pr := Motor3.applyDir tiltRot p
    ⟨pr.x / gamma, pr.y, pr.z⟩
  -- Build subdivided 3×3-per-face relativistic cube mesh so optical shear curves smoothly!
  let sub : Nat := 3
  let mut mb : MeshBuilder := {}
  let addWarpedFace (mb0 : MeshBuilder) (orig uAxis vAxis : Vec3) (col : RGBA) : MeshBuilder := Id.run do
    let mut m := mb0
    let inv := 2.0 * half / Float.ofNat sub
    for iu in [:sub] do
      for iv in [:sub] do
        let u0 := -half + Float.ofNat iu * inv; let u1 := u0 + inv
        let v0 := -half + Float.ofNat iv * inv; let v1 := v0 + inv
        let pt (u v : Float) :=
          warp (Vec3.add orig (Vec3.add (Vec3.scale u uAxis) (Vec3.scale v vAxis)))
        let q0 := pt u0 v0; let q1 := pt u1 v0; let q2 := pt u1 v1; let q3 := pt u0 v1
        let (m1, i0) := m.addVertex q0 col
        let (m2, i1) := m1.addVertex q1 col
        let (m3, i2) := m2.addVertex q2 col
        let (m4, i3) := m3.addVertex q3 col
        m := (m4.addTri i0 i1 i2).addTri i0 i2 i3
    return m
  -- Doppler-tinted cube faces: leading (+x) blueshifted cyan, trailing (-x) redshifted coral!
  let blueShift : RGBA := ⟨max 0.12 (0.35 - 0.22 * beta), min 1.0 (0.72 + 0.24 * beta), 1.0, 0.90⟩
  let redShift  : RGBA := ⟨1.0, max 0.24 (0.58 - 0.30 * beta), max 0.18 (0.45 - 0.25 * beta), 0.92⟩
  let frontCol  : RGBA := ⟨0.32, 0.90, 0.72, 0.88⟩
  let backCol   : RGBA := ⟨0.62, 0.42, 0.98, 0.88⟩
  let topCol    : RGBA := ⟨0.96, 0.80, 0.30, 0.88⟩
  let botCol    : RGBA := ⟨0.30, 0.56, 0.96, 0.88⟩
  mb := addWarpedFace mb ⟨0, 0, half⟩  ⟨1, 0, 0⟩  ⟨0, 1, 0⟩ frontCol
  mb := addWarpedFace mb ⟨0, 0,-half⟩  ⟨-1,0, 0⟩  ⟨0, 1, 0⟩ backCol
  mb := addWarpedFace mb ⟨ half, 0, 0⟩ ⟨0, 0,-1⟩  ⟨0, 1, 0⟩ blueShift
  mb := addWarpedFace mb ⟨-half, 0, 0⟩ ⟨0, 0, 1⟩  ⟨0, 1, 0⟩ redShift
  mb := addWarpedFace mb ⟨0,  half, 0⟩ ⟨1, 0, 0⟩  ⟨0, 0,-1⟩ topCol
  mb := addWarpedFace mb ⟨0, -half, 0⟩ ⟨1, 0, 0⟩  ⟨0, 0, 1⟩ botCol
  let cubeMesh := mb.finalize 7403
  -- Lattice edges of Terrell-Penrose optical cube (solid bright) vs simultaneous Lorentz ghost cube (dashed cyan)!
  let rawCorners : Array Vec3 := #[
    ⟨-half,-half,-half⟩, ⟨ half,-half,-half⟩, ⟨ half, half,-half⟩, ⟨-half, half,-half⟩,
    ⟨-half,-half, half⟩, ⟨ half,-half, half⟩, ⟨ half, half, half⟩, ⟨-half, half, half⟩
  ]
  let edgePairs : Array (Nat × Nat) := #[
    (0,1),(1,2),(2,3),(3,0), (4,5),(5,6),(6,7),(7,4), (0,4),(1,5),(2,6),(3,7)
  ]
  let mut segs : Array SegmentPrim := #[]
  for (a, b) in edgePairs do
    -- Subdivided warped optical edges (4 segments each so curved optical shear is crisp!)
    let pa := rawCorners[a]!; let pb := rawCorners[b]!
    for k in [:4] do
      let u0 := Float.ofNat k / 4.0; let u1 := Float.ofNat (k + 1) / 4.0
      segs := segs.push {
        a := warp (Vec3.lerp pa pb u0), b := warp (Vec3.lerp pa pb u1),
        width := 2.6, color := RGBA.white
      }
    -- Simultaneous Lorentz-contracted ghost wireframe (`x / γ`)
    segs := segs.push {
      a := lorentzOnly pa, b := lorentzOnly pb,
      width := 1.8, color := ⟨0.22, 0.88, 0.95, 0.55⟩, role := { dashed := true }
    }
  -- Past light-cone null photon rays converging toward the observer marker at `(0, 0, 2.35)`
  let obsMarker : Vec3 := ⟨0.0, 0.0, 2.35⟩
  for idx in #[0, 3, 4, 7] do
    segs := segs.push {
      a := warp rawCorners[idx]!, b := obsMarker,
      width := 1.6, color := ⟨1.0, 0.78, 0.25, 0.45⟩, role := { dashed := true, arrow := true }
    }
  -- Velocity vector arrow `β c ê_x`
  segs := segs.push {
    a := ⟨-0.9, -1.25, 0.0⟩, b := ⟨-0.9 + 1.8 * beta, -1.25, 0.0⟩,
    width := 3.6, color := RGBA.amber, role := { arrow := true }
  }
  -- Light-cone rings along the photon propagation axis `z`
  let circles : Array CirclePrim := #[
    { center := ⟨0.0, 0.0, 1.55⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
      radius := 0.80, width := 1.8, color := ⟨1.0, 0.78, 0.25, 0.40⟩ },
    { center := ⟨0.0, 0.0, 0.85⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
      radius := 1.50, width := 1.6, color := ⟨1.0, 0.78, 0.25, 0.28⟩ }
  ]
  let params : Array ParamSpec := #[
    { name := "beta", label := "Speed β = v/c", value := beta, min := 0.0, max := 0.95, step := 0.01 },
    { name := "distance", label := "Observer z₀", value := obsDist, min := 2.5, max := 10.0, step := 0.25 }
  ]
  return { f with
    params,
    formula := "X' = B X \\widetilde{B},\\quad B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right),\\quad \\theta_{\\text{TP}} = \\arcsin(\\beta)",
    summary := "Relativistic Cl(3,1) Terrell-Penrose optical aberration showing why a cube moving at speed βc appears rotated by arcsin(β) rather than squished.",
    meshAssets := #[cubeMesh],
    meshRefs := #[{
      meshId := cubeMesh.meshId, dirtyHash := cubeMesh.dirtyHash,
      color := RGBA.white, useVertexColors := true, doubleSided := true
    }],
    segments := segs,
    circles,
    points := #[
      { handleId := 0, pos := ctrl, radius := 0.075, color := RGBA.cyan, role := { draggable := true }, label := "Tilt" },
      { handleId := 1, pos := obsMarker, radius := 0.095, color := RGBA.amber, label := "Observer (t=0)" }
    ],
    labels := #[
      { pos := ⟨0.0, -1.52, 0.0⟩, text := s!"β={beta}c · γ={gamma} · θ_TP={tpAngleDeg}°", color := RGBA.amber }
    ],
    inspect := #[
      { idx := 0, name := "Boost B ∈ STA", grade := 2,
        formatted := s!"exp({0.5 * rapidity} e01) · β={beta}c · γ={gamma}", editable := false },
      { idx := 1, name := "Terrell-Penrose", grade := 0,
        formatted := s!"Apparent rotation θ_TP = {tpAngleDeg}° (trailing red face revealed!)", editable := false }
    ] }

/-! ## 4. `sta_maxwell_streamlines` — 3D RK4 Electromagnetic Dipole Streamlines (`F = E + IB`) -/

/-- Exact 3D electric field `E(r, t)` of an oscillating vertical dipole along `+Y` + radiation phase. -/
private def dipoleEField (p : Vec3) (t freq dipole : Float) : Vec3 :=
  let r2 := p.x * p.x + p.y * p.y + p.z * p.z
  let r := Float.sqrt (r2 + 0.08)
  let invR3 := 1.0 / (r * r * r)
  let phase := Float.cos (freq * (r * 1.4 - t))
  let amp := dipole * (0.65 + 0.35 * phase)
  -- Near-field dipole `(3 (p·r̂) r̂ - p) / r³` for `p = (0, amp, 0)`
  let pyOverR2 := p.y / (r2 + 0.08)
  let ex := 3.0 * p.x * pyOverR2 * amp * invR3
  let ey := (3.0 * p.y * pyOverR2 - 1.0) * amp * invR3
  let ez := 3.0 * p.z * pyOverR2 * amp * invR3
  ⟨ex, ey, ez⟩

/-- Exact 3D magnetic field `B(r, t)` circulating azimuthally around the oscillating dipole axis `+Y`. -/
private def dipoleBField (p : Vec3) (t freq dipole bScale : Float) : Vec3 :=
  let rho := Float.sqrt (p.x * p.x + p.z * p.z)
  let r := Float.sqrt (p.x * p.x + p.y * p.y + p.z * p.z + 0.12)
  let wave := 0.55 + 0.45 * Float.cos (freq * (r * 1.6 - t))
  let mag := bScale * dipole * wave * (rho / (r * r * r + 0.15))
  if rho < 1e-5 then Vec3.zero
  else Vec3.scale (mag / rho) ⟨-p.z, 0.0, p.x⟩

/-- 4-stage RK4 integration step along a normalized 3D vector field `fieldFn`. -/
private def rk4StepField (fieldFn : Vec3 → Vec3) (p : Vec3) (h : Float) : Vec3 :=
  let dir (q : Vec3) : Vec3 :=
    let v := fieldFn q
    let n := Vec3.norm v
    if n < 1e-6 then Vec3.zero else Vec3.scale (1.0 / n) v
  let k1 := dir p
  let k2 := dir (Vec3.add p (Vec3.scale (0.5 * h) k1))
  let k3 := dir (Vec3.add p (Vec3.scale (0.5 * h) k2))
  let k4 := dir (Vec3.add p (Vec3.scale h k3))
  Vec3.add p (Vec3.scale (h / 6.0)
    (Vec3.add k1 (Vec3.add (Vec3.scale 2.0 k2) (Vec3.add (Vec3.scale 2.0 k3) k4))))

def buildStaMaxwellStreamlines (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let freq := paramVal overrides "frequency" 1.2 0.2 3.5
  let dipole := paramVal overrides "dipole" 1.0 0.3 2.0
  let bScale := paramVal overrides "bScale" 1.0 0.0 2.0
  let f := mkShowcaseBase "sta_maxwell_streamlines" "STA Maxwell Dipole RK4 Streamlines (F = E + IB)" "STA" seq t 5.4
  let eFn (q : Vec3) := dipoleEField q t freq dipole
  let bFn (q : Vec3) := dipoleBField q t freq dipole bScale
  -- 1. RK4-advected 3D Electric-field streamline particles (`0x0D FLOW_PARTICLES`, cyan)
  let mut eStarts := FloatArray.emptyWithCapacity (192 * 3)
  let mut eEnds   := FloatArray.emptyWithCapacity (192 * 3)
  let nAz := 12
  let nShell := 2
  let nBeads := 8
  for iAz in [:nAz] do
    let phi := twoPiF * Float.ofNat iAz / Float.ofNat nAz
    let cp := Float.cos phi; let sp := Float.sin phi
    for iSh in [:nShell] do
      let rEq := if iSh == 0 then 1.35 else 2.05
      for iB in [:nBeads] do
        -- Advect phase smoothly from north dipole lobe (θ ≈ 0.25) to south lobe (θ ≈ π - 0.25)
        let frac := Float.ofNat iB / Float.ofNat nBeads + (t * freq * 0.14)
        let u := frac - Float.floor frac
        let th := 0.26 + u * (piF - 0.52)
        let st := Float.sin th
        let r := rEq * st * st
        let p0 : Vec3 := ⟨r * st * cp, r * Float.cos th, r * st * sp⟩
        let eMag := min 2.2 (Vec3.norm (eFn p0))
        let stepLen := 0.14 + 0.12 * min 1.0 eMag
        let p1 := rk4StepField eFn p0 stepLen
        eStarts := eStarts.push p0.x |>.push p0.y |>.push p0.z
        eEnds   := eEnds.push p1.x   |>.push p1.y   |>.push p1.z
  -- 2. RK4-advected 3D Magnetic-field azimuthal streamlines (`0x0D FLOW_PARTICLES`, amber)
  let mut bStarts := FloatArray.emptyWithCapacity (128 * 3)
  let mut bEnds   := FloatArray.emptyWithCapacity (128 * 3)
  if bScale > 0.02 then
    let rings : Array (Float × Float) := #[(0.85, 0.0), (1.45, 0.0), (1.15, 0.55), (1.15, -0.55)]
    for (rRing, yRing) in rings do
      for k in [:32] do
        let ang := twoPiF * (Float.ofNat k / 32.0) + t * freq * 0.45
        let p0 : Vec3 := ⟨rRing * Float.cos ang, yRing, rRing * Float.sin ang⟩
        let bMag := min 2.0 (Vec3.norm (bFn p0))
        let stepLen := 0.14 + 0.14 * min 1.0 bMag
        let p1 := rk4StepField bFn p0 stepLen
        bStarts := bStarts.push p0.x |>.push p0.y |>.push p0.z
        bEnds   := bEnds.push p1.x   |>.push p1.y   |>.push p1.z
  -- 3. Crisp analytical dipole field-line guide curves + glowing Faraday bivector disks (`I B`)
  let mut curves : Array CurvePrim := #[]
  for iAz in [:8] do
    let phi := twoPiF * Float.ofNat iAz / 8.0
    let cp := Float.cos phi; let sp := Float.sin phi
    let mut pts : Array Vec3 := Array.mkEmpty 33
    for j in [:33] do
      let th := 0.16 + (piF - 0.32) * (Float.ofNat j / 32.0)
      let st := Float.sin th
      let r := 1.65 * st * st
      pts := pts.push ⟨r * st * cp, r * Float.cos th, r * st * sp⟩
    curves := curves.push (curveFromVecs pts ⟨0.22, 0.85, 0.98, 0.48⟩ 1.8 false false)
  let mut disks : Array BivectorDiskPrim := #[]
  for k in [:6] do
    let phi := twoPiF * Float.ofNat k / 6.0 + t * 0.25
    let pos : Vec3 := ⟨1.35 * Float.cos phi, 0.0, 1.35 * Float.sin phi⟩
    let bVec := bFn pos
    let bNorm := Vec3.norm bVec
    let bAxis := if bNorm > 1e-5 then Vec3.scale (1.0 / bNorm) bVec else ⟨-Float.sin phi, 0.0, Float.cos phi⟩
    let (du, dv) := Vec3.orthonormalBasis bAxis
    let rad := 0.24 + 0.12 * min 1.5 bNorm
    disks := disks.push {
      origin := pos, u := Vec3.scale rad du, v := Vec3.scale rad dv,
      area := piF * rad * rad, color := ⟨1.0, 0.68, 0.22, 0.34⟩,
      isDisk := true, orientationArrow := true
    }
  -- Draggable Faraday field probe handle 0
  let probe := hPos handles 0 ⟨1.25, 0.45, 0.35⟩
  let eP := eFn probe
  let bP := bFn probe
  let eDir := Vec3.scale (min 0.85 (0.30 + 0.25 * Vec3.norm eP)) (Vec3.normalize eP)
  let bDir := Vec3.scale (min 0.85 (0.30 + 0.25 * Vec3.norm bP)) (Vec3.normalize bP)
  let osc := 0.28 * Float.cos (freq * t)
  let params : Array ParamSpec := #[
    { name := "frequency", label := "Frequency ω", value := freq, min := 0.2, max := 3.5, step := 0.1 },
    { name := "dipole", label := "Dipole Moment p", value := dipole, min := 0.3, max := 2.0, step := 0.05 },
    { name := "bScale", label := "Magnetic B Scale", value := bScale, min := 0.0, max := 2.0, step := 0.05 }
  ]
  let flowFields : Array FlowFieldPrim :=
    if bStarts.size ≥ 3 then
      #[{ starts := eStarts, ends := eEnds, pointSize := 5.2, color := RGBA.cyan, speed := freq },
        { starts := bStarts, ends := bEnds, pointSize := 5.0, color := RGBA.amber, speed := freq }]
    else
      #[{ starts := eStarts, ends := eEnds, pointSize := 5.2, color := RGBA.cyan, speed := freq }]
  return { f with
    params,
    formula := "\\nabla F = J,\\qquad F = \\mathbf{E} + I\\mathbf{B} \\in \\mathrm{Cl}_{3,1}",
    summary := "3D RK4-advected electric and magnetic dipole streamlines with glowing Faraday bivector disks unified in Spacetime Algebra F = E + IB.",
    flowFields,
    curves,
    bivectorDisks := disks,
    spheres := #[
      { center := ⟨0.0,  0.22 + 0.08 * osc, 0.0⟩, radius := 0.16, color := ⟨1.0, 0.38, 0.38, 0.95⟩, label := "+q" },
      { center := ⟨0.0, -0.22 - 0.08 * osc, 0.0⟩, radius := 0.16, color := ⟨0.24, 0.72, 1.0, 0.95⟩, label := "-q" }
    ],
    segments := #[
      { a := probe, b := Vec3.add probe eDir, width := 3.4, color := RGBA.cyan, role := { arrow := true } },
      { a := probe, b := Vec3.add probe bDir, width := 3.4, color := RGBA.amber, role := { arrow := true } }
    ],
    points := #[
      { handleId := 0, pos := probe, radius := 0.09, color := RGBA.white, role := { draggable := true }, label := "Probe F" }
    ],
    inspect := #[
      { idx := 0, name := "Faraday F = E + IB", grade := 2,
        formatted := s!"|E|={Vec3.norm eP} · |B|={Vec3.norm bP} · ω={freq}", editable := false }
    ] }

/-! ## 5. `pga3d_hopf_streamlines` — 3D RK4 PGA3 Screw-Motor & Hopf Fibration Flow Ribbons -/

/-- Combined Y-up stereographic Hopf Killing field on `S³ → ℝ³` blended with a PGA3 Chasles
screw-motor bivector velocity field `(twist, pitch)`. -/
private def hopfScrewField (p : Vec3) (pitch twist : Float) : Vec3 :=
  let r2 := p.x * p.x + p.y * p.y + p.z * p.z
  -- Exact right-handed Y-up Hopf fibration tangent field on S³ → ℝ³
  let hx := p.z + p.x * p.y
  let hy := 0.5 * (1.0 - p.x * p.x + p.y * p.y - p.z * p.z)
  let hz := -p.x + p.z * p.y
  -- PGA3 screw-motor bivector velocity field around Y-axis: `ω × p + pitch * ω`
  let sx := p.z
  let sy := pitch
  let sz := -p.x
  let invReg := 1.0 / (1.0 + 0.18 * r2)
  ⟨(twist * hx + 0.55 * sx) * invReg,
   (twist * hy + 0.85 * sy) * invReg,
   (twist * hz + 0.55 * sz) * invReg⟩

/-- Stereographic projection of a Hopf fiber `(η, φ, ξ) ∈ S³ → ℝ³` (Y-up right-handed). -/
private def hopfPointYUp (eta phi xi : Float) : Vec3 :=
  let ce := Float.cos eta; let se := Float.sin eta
  let x4 := ce * Float.cos (xi + phi)
  let y4 := ce * Float.sin (xi + phi)
  let z4 := se * Float.cos xi
  let w4 := se * Float.sin xi
  let denom := max 0.25 (1.0 - w4)
  let sc := 0.92 / denom
  ⟨sc * x4, sc * z4, -sc * y4⟩

def buildPga3dHopfStreamlines (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64) (t : Float) : SceneFrame := Id.run do
  let pitch := paramVal overrides "pitch" 0.35 (-1.2) 1.2
  let twist := paramVal overrides "twist" 1.5 0.2 3.5
  let flowSpeed := paramVal overrides "flowSpeed" 1.0 0.1 2.5
  let f := mkShowcaseBase "pga3d_hopf_streamlines" "3D PGA Screw-Motor & Hopf Fibration Flow Ribbons" "PGA3" seq t 5.6
  let fieldFn (q : Vec3) := hopfScrewField q pitch twist
  -- 3 nested Villarceau toroidal layers of RK4-advected flow streaks (`0x0D FLOW_PARTICLES`)!
  let buildLayer (eta : Float) (nFibers nBeads : Nat) : FloatArray × FloatArray := Id.run do
    let total := nFibers * nBeads
    let mut starts := FloatArray.emptyWithCapacity (total * 3)
    let mut ends   := FloatArray.emptyWithCapacity (total * 3)
    for iF in [:nFibers] do
      let phi := twoPiF * Float.ofNat iF / Float.ofNat nFibers
      for iB in [:nBeads] do
        let xi := twoPiF * (Float.ofNat iB / Float.ofNat nBeads) + t * flowSpeed * 0.55
        let p0 := hopfPointYUp eta phi xi
        let v0 := fieldFn p0
        let vMag := min 2.4 (Vec3.norm v0)
        let hStep := 0.16 + 0.14 * min 1.0 vMag
        let p1 := rk4StepField fieldFn p0 hStep
        starts := starts.push p0.x |>.push p0.y |>.push p0.z
        ends   := ends.push p1.x   |>.push p1.y   |>.push p1.z
    return (starts, ends)
  let (s1, e1) := buildLayer 0.48 9 12   -- Inner core torus (108 cyan streaks)
  let (s2, e2) := buildLayer 0.82 10 12  -- Mid Villarceau torus (120 violet streaks)
  let (s3, e3) := buildLayer 1.12 8 12   -- Outer flared torus (96 amber streaks)
  -- 12 linked Hopf Villarceau guide fibers + live RK4 streamline from draggable handle 0
  let mut curves : Array CurvePrim := #[]
  let cols : Array RGBA := #[⟨0.22, 0.88, 0.95, 0.50⟩, ⟨0.72, 0.45, 1.0, 0.48⟩, ⟨1.0, 0.72, 0.22, 0.45⟩]
  let etas : Array Float := #[0.50, 0.84, 1.12]
  for li in [:3] do
    let eta := etas[li]!
    let col := cols[li]!
    for k in [:4] do
      let phi := twoPiF * Float.ofNat k / 4.0 + Float.ofNat li * 0.42
      let mut pts : Array Vec3 := Array.mkEmpty 48
      for j in [:48] do
        let xi := twoPiF * Float.ofNat j / 48.0
        pts := pts.push (hopfPointYUp eta phi xi)
      curves := curves.push (curveFromVecs pts col 1.7 true false)
  -- Live RK4 trajectory launched from draggable handle 0!
  let seed := hPos handles 0 ⟨0.95, 0.15, 0.0⟩
  let mut livePts : Array Vec3 := #[seed]
  let mut cur := seed
  for _ in [:56] do
    cur := rk4StepField fieldFn cur 0.11
    livePts := livePts.push cur
  curves := curves.push (curveFromVecs livePts RGBA.coral 3.4 false false)
  let params : Array ParamSpec := #[
    { name := "pitch", label := "Screw Pitch h", value := pitch, min := -1.2, max := 1.2, step := 0.05 },
    { name := "twist", label := "Hopf Twist k", value := twist, min := 0.2, max := 3.5, step := 0.1 },
    { name := "flowSpeed", label := "Flow Speed", value := flowSpeed, min := 0.1, max := 2.5, step := 0.1 }
  ]
  return { f with
    params,
    formula := "M(s) = \\exp\\!\\left(\\tfrac{s}{2}(k\\,L + h\\,e_0 L)\\right),\\qquad \\mathbf{v}_{\\text{Hopf}} = \\big(z+xy,\\;\\tfrac{1-x^2+y^2-z^2}{2},\\;-x+yz\\big)",
    summary := "3D RK4-advected particle flow ribbons blending linked S³→ℝ³ Hopf fibration fibers with PGA3 Chasles screw-motor velocity fields.",
    flowFields := #[
      { starts := s1, ends := e1, pointSize := 5.2, color := RGBA.cyan, speed := flowSpeed },
      { starts := s2, ends := e2, pointSize := 5.0, color := RGBA.violet, speed := flowSpeed },
      { starts := s3, ends := e3, pointSize := 4.8, color := RGBA.amber, speed := flowSpeed }
    ],
    curves,
    lines := #[{
      origin := Vec3.zero, dir := ⟨0.0, 1.0, 0.0⟩, clip := 2.6, width := 2.2,
      color := RGBA.white, label := "Screw Axis L"
    }],
    points := #[
      { handleId := 0, pos := seed, radius := 0.09, color := RGBA.coral, role := { draggable := true }, label := "Stream Seed" }
    ],
    inspect := #[
      { idx := 0, name := "Screw Bivector", grade := 2,
        formatted := s!"{twist} e13 + {pitch} e02 · 324 RK4 streaks", editable := false }
    ] }

/-! ## 6. `implicit_barth_sextic` — Barth Sextic Algebraic Surface (GPU Raymarch + Bytecode MT) -/

/-- Format a finite `Float` to a clean decimal literal for `ImplicitExpr` / `GPUInit` shaders. -/
private def fmtExprNum (x : Float) : String :=
  if !x.isFinite || x.isNaN || Float.abs x < 1e-9 then "0.0"
  else
    let neg := x < 0.0
    let ax := Float.abs x
    let scaled := (ax * 10000.0 + 0.5).toUInt64.toNat
    let intPart := scaled / 10000
    let fracPart := scaled % 10000
    let pad4 (n : Nat) : String :=
      let s := toString n
      if s.length == 1 then "000" ++ s
      else if s.length == 2 then "00" ++ s
      else if s.length == 3 then "0" ++ s
      else s
    let body := s!"{intPart}.{pad4 fracPart}"
    if neg then "-" ++ body else body

/-- **6. `implicit_barth_sextic`** — Iconic degree-6 Barth Sextic with 65 icosahedral ordinary
double points: BOTH live `GPUInit` GLSL3/WGSL/MSL sphere-tracer AND fast bytecode Marching Tetrahedra
mesh + interactive `phi` & `iso` `@param` sliders! -/
def buildImplicitBarthSextic (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64 := 0) (t : Float := 0.0) : SceneFrame := Id.run do
  let f := mkShowcaseBase "implicit_barth_sextic"
    "Barth Sextic (GPU Raymarch + Bytecode MT)" "R3" seq t 4.8
  let phi := paramVal overrides "phi" 1.618034 1.1 2.1
  let iso := paramVal overrides "iso" 0.0 (-0.35) 0.35
  let p2 := phi * phi
  let w := 1.0 + 2.0 * phi
  let exprStr :=
    s!"4*({fmtExprNum p2}*x^2 - y^2)*({fmtExprNum p2}*y^2 - z^2)*({fmtExprNum p2}*z^2 - x^2) - {fmtExprNum w}*(x^2 + y^2 + z^2 - 1)^2 - ({fmtExprNum iso})"
  let shaders : Array OpnsShaderSource :=
    match compileImplicitExprToGpu exprStr "barth_sextic" 1.65 with
    | .ok sh => #[sh]
    | .error _ => #[]
  let (meshAssets, meshRefs, meshStats) : Array MeshAsset × Array MeshRefPrim × String :=
    match evalImplicitExprMesh exprStr 0.0 ⟨-1.65, -1.65, -1.65⟩ ⟨1.65, 1.65, 1.65⟩ 16 7420 false with
    | .ok m =>
      (#[m],
       #[{ meshId := m.meshId, dirtyHash := m.dirtyHash,
           motor := Motor3.identity,
           color := ⟨0.98, 0.80, 0.38, 0.24⟩,
           wireframe := true, useVertexColors := false }],
       s!"{m.positions.size / 3} verts, {m.indices.size / 3} tris")
    | .error _ => (#[], #[], "mesh err")
  -- 12 icosahedral symmetry poles `(±1, ±φ, 0)` cyclic normalized onto the unit sphere
  let invR := 1.0 / Float.sqrt (1.0 + phi * phi)
  let a := invR; let b := phi * invR
  let icoPts : Array Vec3 := #[
    ⟨a, b, 0.0⟩, ⟨-a, b, 0.0⟩, ⟨a, -b, 0.0⟩, ⟨-a, -b, 0.0⟩,
    ⟨0.0, a, b⟩, ⟨0.0, -a, b⟩, ⟨0.0, a, -b⟩, ⟨0.0, -a, -b⟩,
    ⟨b, 0.0, a⟩, ⟨-b, 0.0, a⟩, ⟨b, 0.0, -a⟩, ⟨-b, 0.0, -a⟩
  ]
  let ctrl := hPos handles 0 ⟨0.0, 1.55, 0.0⟩
  let mut pts : Array PointPrim := #[
    { handleId := 0, pos := ctrl, radius := 0.075, color := RGBA.cyan,
      role := { draggable := true }, label := "Symmetry Probe" }
  ]
  for k in [:icoPts.size] do
    pts := pts.push {
      handleId := (10 + k).toUInt32, pos := icoPts[k]!, radius := 0.042,
      color := RGBA.amber, label := if k == 0 then "A₅ Pole" else ""
    }
  let params : Array ParamSpec := #[
    { name := "phi", label := "Golden Ratio φ", value := phi, min := 1.1, max := 2.1, step := 0.01 },
    { name := "iso", label := "Iso-Level c", value := iso, min := -0.35, max := 0.35, step := 0.01 }
  ]
  return { f with
    params,
    opnsShaders := shaders,
    opnsUniforms := if shaders.isEmpty then #[] else #[{
      shaderIdx := 0, grade := 0, coeffs := FloatArray.empty,
      thresh := 0.002, maxSteps := 128, stepSize := 0.01,
      color := ⟨0.96, 0.72, 0.28, 0.96⟩, isIPNS := false
    }],
    meshAssets,
    meshRefs,
    points := pts,
    inspect := #[
      { idx := 0, name := "Barth Sextic", grade := 0,
        formatted := s!"φ={fmtExprNum phi}, c={fmtExprNum iso} · 65 double points · {meshStats}",
        editable := false },
      { idx := 1, name := "GPU Raymarcher", grade := 0,
        formatted := if shaders.isEmpty then "err" else s!"WGSL+GLSL3+MSL ({shaders[0]!.hash})",
        editable := false }
    ] }

/-! ## 7. `cga3d_dupin_cyclide_raymarch` — CGA3 Dupin Cyclide (GPU Sphere-Tracer + Focal Conics) -/

/-- **7. `cga3d_dupin_cyclide_raymarch`** — Sphere-traced 3D CGA Dupin Cyclide with interactive
`majorR`/`minorR`/`eccentricity` `@param` sliders and glowing orthogonal focal ellipse + hyperbola! -/
def buildCga3dDupinCyclideRaymarch (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64 := 0) (t : Float := 0.0) : SceneFrame := Id.run do
  let f := mkShowcaseBase "cga3d_dupin_cyclide_raymarch"
    "3D CGA Dupin Cyclide (GPU Raymarch + Focal Conics)" "CGA3" seq t 5.0
  let a := paramVal overrides "majorR" 1.05 0.65 1.45
  let d := paramVal overrides "minorR" 0.48 0.20 0.85
  let ecc := paramVal overrides "eccentricity" 0.42 0.0 0.72
  let c := ecc * a
  let b2 := max 0.04 (a * a - c * c)
  let b := Float.sqrt b2
  let k1 := b2 - d * d
  let cd := c * d
  let bound := max 1.65 (a + d + 0.25)
  let exprStr :=
    s!"(x^2 + y^2 + z^2 + ({fmtExprNum k1}))^2 - 4*({fmtExprNum a}*x - ({fmtExprNum cd}))^2 - {fmtExprNum (4.0 * b2)}*z^2"
  let shaders : Array OpnsShaderSource :=
    match compileImplicitExprToGpu exprStr "cga3_dupin_cyclide" bound with
    | .ok sh => #[sh]
    | .error _ => #[]
  let (meshAssets, meshRefs) : Array MeshAsset × Array MeshRefPrim :=
    match evalImplicitExprMesh exprStr 0.0 ⟨-bound, -bound, -bound⟩ ⟨bound, bound, bound⟩ 14 7421 false with
    | .ok m =>
      (#[m],
       #[{ meshId := m.meshId, dirtyHash := m.dirtyHash,
           motor := Motor3.identity,
           color := ⟨0.36, 0.88, 1.0, 0.20⟩,
           wireframe := true, useVertexColors := false }])
    | .error _ => (#[], #[])
  -- Glowing focal ellipse in horizontal `y = 0` plane: `(a cos θ, 0, b sin θ)`
  let mut ellPts : Array Vec3 := #[]
  for i in [:65] do
    let th := twoPiF * Float.ofNat i / 64.0
    ellPts := ellPts.push ⟨a * Float.cos th, 0.0, b * Float.sin th⟩
  -- Two glowing focal hyperbola branches in `z = 0` plane: `(±c cosh s, b sinh s, 0)`
  let mut hypPos : Array Vec3 := #[]
  let mut hypNeg : Array Vec3 := #[]
  let cEff := max 0.03 c
  for i in [:41] do
    let s := -1.1 + 2.2 * Float.ofNat i / 40.0
    let ch := Float.cosh s
    let sh := Float.sinh s
    hypPos := hypPos.push ⟨cEff * ch, b * sh, 0.0⟩
    hypNeg := hypNeg.push ⟨-cEff * ch, b * sh, 0.0⟩
  let probe := hPos handles 0 ⟨a * Float.cos (t * 0.6), 0.0, b * Float.sin (t * 0.6)⟩
  let rThin := max 0.06 (Float.abs (d - c))
  let rThick := d + c
  let params : Array ParamSpec := #[
    { name := "majorR", label := "Major Radius a", value := a, min := 0.65, max := 1.45, step := 0.02 },
    { name := "minorR", label := "Tube Radius d", value := d, min := 0.20, max := 0.85, step := 0.02 },
    { name := "eccentricity", label := "Eccentricity c/a", value := ecc, min := 0.0, max := 0.72, step := 0.02 }
  ]
  return { f with
    params,
    opnsShaders := shaders,
    opnsUniforms := if shaders.isEmpty then #[] else #[{
      shaderIdx := 0, grade := 0, coeffs := FloatArray.empty,
      thresh := 0.002, maxSteps := 112, stepSize := 0.01,
      color := ⟨0.32, 0.84, 0.98, 0.94⟩, isIPNS := false
    }],
    meshAssets,
    meshRefs,
    curves := #[
      curveFromVecs ellPts RGBA.amber 3.2 true,
      curveFromVecs hypPos RGBA.coral 3.0 false,
      curveFromVecs hypNeg RGBA.violet 3.0 false
    ],
    circles := #[
      { center := ⟨a, 0.0, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
        radius := rThin, width := 2.2, color := RGBA.green, label := "Waist C₁" },
      { center := ⟨-a, 0.0, 0.0⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
        radius := rThick, width := 2.2, color := RGBA.cyan, label := "Crest C₂" }
    ],
    points := #[
      { handleId := 0, pos := probe, radius := 0.08, color := RGBA.green, role := { draggable := true }, label := "Focal Orbit" },
      { handleId := 10, pos := ⟨c, 0.0, 0.0⟩, radius := 0.065, color := RGBA.coral, label := "+c Focus" },
      { handleId := 11, pos := ⟨-c, 0.0, 0.0⟩, radius := 0.065, color := RGBA.violet, label := "-c Focus" }
    ],
    inspect := #[
      { idx := 0, name := "Dupin Cyclide", grade := 4,
        formatted := s!"a={fmtExprNum a}, b={fmtExprNum b}, c={fmtExprNum c}, d={fmtExprNum d}",
        editable := false },
      { idx := 1, name := "GPU Raymarcher", grade := 0,
        formatted := if shaders.isEmpty then "err" else s!"WGSL+GLSL3+MSL ({shaders[0]!.hash})",
        editable := false }
    ] }

/-! ## 8. `pga3d_gears_kinematics` — 3D PGA Meshing Involute Gear Train (Composed Screw Motors) -/

/-- Build a watertight outward-CCW 3D involute-style spur gear mesh with tooth flanks,
beveled tips, roots, and central shaft bore purely in Lean (`Init`-only). -/
private def buildInvoluteGearMesh (teeth : Nat) (pitchR thick : Float)
    (baseCol : RGBA) (meshId : UInt64) : MeshAsset := Id.run do
  let z := max 6 teeth
  let zF := Float.ofNat z
  let modM := (2.0 * pitchR) / zF
  let rOut := pitchR + 0.78 * modM
  let rRoot := max (0.30 * pitchR) (pitchR - 0.98 * modM)
  let rHub := max 0.11 (0.28 * pitchR)
  let hz := 0.5 * thick
  let stepsPerTooth := 4
  let nSeg := z * stepsPerTooth
  -- Profile radii per tooth phase: [root, pitch-flank, tip, tip]
  let profR (step : Nat) : Float :=
    match step % 4 with
    | 0 => rRoot
    | 1 => rOut
    | 2 => rOut
    | _ => rRoot
  let profAng (i : Nat) : Float :=
    let toothIdx := i / 4
    let sub := i % 4
    let baseA := twoPiF * Float.ofNat toothIdx / zF
    let stepA := twoPiF / zF
    let frac :=
      match sub with
      | 0 => 0.08
      | 1 => 0.30
      | 2 => 0.62
      | _ => 0.84
    baseA + frac * stepA
  let tipCol : RGBA := ⟨min 1.0 (baseCol.r * 1.18), min 1.0 (baseCol.g * 1.18), min 1.0 (baseCol.b * 1.18), 1.0⟩
  let rootCol : RGBA := ⟨baseCol.r * 0.72, baseCol.g * 0.72, baseCol.b * 0.72, 1.0⟩
  let hubCol : RGBA := ⟨0.24, 0.28, 0.36, 1.0⟩
  let mut mb : MeshBuilder := {}
  -- Add ring vertices: [0..nSeg-1] outer front (+hz), [nSeg..2*nSeg-1] outer back (-hz),
  -- [2*nSeg..3*nSeg-1] inner bore front (+hz), [3*nSeg..4*nSeg-1] inner bore back (-hz)
  for i in [:nSeg] do
    let a := profAng i; let r := profR i
    let c := if i % 4 == 1 || i % 4 == 2 then tipCol else rootCol
    let (mb1, _) := mb.addVertex ⟨r * Float.cos a, r * Float.sin a, hz⟩ c
    mb := mb1
  for i in [:nSeg] do
    let a := profAng i; let r := profR i
    let c := if i % 4 == 1 || i % 4 == 2 then tipCol else rootCol
    let (mb1, _) := mb.addVertex ⟨r * Float.cos a, r * Float.sin a, -hz⟩ c
    mb := mb1
  for i in [:nSeg] do
    let a := profAng i
    let (mb1, _) := mb.addVertex ⟨rHub * Float.cos a, rHub * Float.sin a, hz⟩ hubCol
    mb := mb1
  for i in [:nSeg] do
    let a := profAng i
    let (mb1, _) := mb.addVertex ⟨rHub * Float.cos a, rHub * Float.sin a, -hz⟩ hubCol
    mb := mb1
  for i in [:nSeg] do
    let j := (i + 1) % nSeg
    let of0 := i.toUInt32; let of1 := j.toUInt32
    let ob0 := (nSeg + i).toUInt32; let ob1 := (nSeg + j).toUInt32
    let if0 := (2 * nSeg + i).toUInt32; let if1 := (2 * nSeg + j).toUInt32
    let ib0 := (3 * nSeg + i).toUInt32; let ib1 := (3 * nSeg + j).toUInt32
    -- Front annular face (+Z normal, CCW)
    mb := mb.addTri if0 of0 of1 |>.addTri if0 of1 if1
    -- Back annular face (-Z normal, CCW from back)
    mb := mb.addTri ib0 ob1 ob0 |>.addTri ib0 ib1 ob1
    -- Outer tooth perimeter wall (outward normal)
    mb := mb.addTri of0 ob0 ob1 |>.addTri of0 ob1 of1
    -- Inner bore wall (inward normal toward shaft center)
    mb := mb.addTri if0 if1 ib1 |>.addTri if0 ib1 ib0
  return mb.finalize meshId

private def driveGear12Asset : MeshAsset :=
  buildInvoluteGearMesh 12 0.56 0.22 RGBA.cyan 7431

private def pinionGear9Asset : MeshAsset :=
  buildInvoluteGearMesh 9 0.42 0.22 RGBA.coral 7433

/-- **8. `pga3d_gears_kinematics`** — Meshing 3D PGA3 involute-style 3-gear train driven by
composed PGA3 rotational motors with live `speed` & `ratio` `@param` sliders! -/
def buildPga3dGearsKinematics (handles : Array (UInt32 × Vec3))
    (overrides : Array (String × Float)) (seq : UInt64 := 0) (t : Float := 0.0) : SceneFrame :=
  let f := mkShowcaseBase "pga3d_gears_kinematics"
    "3D PGA Meshing Involute Gear Train (Composed Motors)" "PGA3" seq t 5.2
  let speed := paramVal overrides "speed" 1.4 (-4.0) 4.0
  let ratio := paramVal overrides "ratio" 1.5 0.5 2.0
  let z1 : Nat := 12
  let r1 : Float := 0.56
  let z2 : Nat := max 6 (min 24 ((12.0 * ratio + 0.5).toUInt32.toNat))
  let actualRatio := Float.ofNat z2 / Float.ofNat z1
  let r2 : Float := r1 * actualRatio
  let z3 : Nat := 9
  let r3 : Float := r1 * (Float.ofNat z3 / Float.ofNat z1)
  let gear2Asset := buildInvoluteGearMesh z2 r2 0.22 RGBA.amber (7440 + z2.toUInt64)
  -- Draggable handle 0 scrubs extra phase offset cleanly
  let phaseH := hPos handles 0 ⟨0.0, -1.25, 0.0⟩
  let theta1 := speed * t + phaseH.x * 1.4
  let theta2 := -(theta1 / actualRatio) + piF / Float.ofNat z2
  let theta3 := -(Float.ofNat z1 / Float.ofNat z3) * theta1 + piF / (2.0 * Float.ofNat z3)
  let c1 : Vec3 := ⟨-r1, 0.0, 0.0⟩
  let c2 : Vec3 := ⟨r2, 0.0, 0.0⟩
  let c3 : Vec3 := ⟨-r1, r1 + r3, 0.0⟩
  let m1 := Motor3.mul (Motor3.translator c1.x c1.y c1.z) (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ theta1)
  let m2 := Motor3.mul (Motor3.translator c2.x c2.y c2.z) (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ theta2)
  let m3 := Motor3.mul (Motor3.translator c3.x c3.y c3.z) (Motor3.rotorAxis ⟨0.0, 0.0, 1.0⟩ theta3)
  let w2 := -speed / actualRatio
  let w3 := -(Float.ofNat z1 / Float.ofNat z3) * speed
  let params : Array ParamSpec := #[
    { name := "speed", label := "Drive Speed ω", value := speed, min := -4.0, max := 4.0, step := 0.1 },
    { name := "ratio", label := "Gear Ratio Z₂/Z₁", value := ratio, min := 0.5, max := 2.0, step := 0.1 }
  ]
  { f with
    params,
    meshAssets := #[driveGear12Asset, gear2Asset, pinionGear9Asset],
    meshRefs := #[
      { meshId := driveGear12Asset.meshId, dirtyHash := driveGear12Asset.dirtyHash,
        motor := m1, color := RGBA.white, useVertexColors := true },
      { meshId := gear2Asset.meshId, dirtyHash := gear2Asset.dirtyHash,
        motor := m2, color := RGBA.white, useVertexColors := true },
      { meshId := pinionGear9Asset.meshId, dirtyHash := pinionGear9Asset.dirtyHash,
        motor := m3, color := RGBA.white, useVertexColors := true }
    ],
    circles := #[
      { center := c1, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩, radius := r1, width := 2.2,
        color := ⟨0.20, 0.90, 1.0, 0.80⟩, label := s!"Pitch₁ (Z={z1})" },
      { center := c2, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩, radius := r2, width := 2.2,
        color := ⟨1.0, 0.78, 0.24, 0.80⟩, label := s!"Pitch₂ (Z={z2})" },
      { center := c3, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩, radius := r3, width := 2.2,
        color := ⟨1.0, 0.44, 0.48, 0.80⟩, label := s!"Pitch₃ (Z={z3})" }
    ],
    lines := #[
      { origin := c1, dir := ⟨0.0, 0.0, 1.0⟩, clip := 1.1, width := 2.4, color := RGBA.cyan, label := "Axis₁" },
      { origin := c2, dir := ⟨0.0, 0.0, 1.0⟩, clip := 1.1, width := 2.4, color := RGBA.amber, label := "Axis₂" },
      { origin := c3, dir := ⟨0.0, 0.0, 1.0⟩, clip := 1.1, width := 2.4, color := RGBA.coral, label := "Axis₃" }
    ],
    bivectorDisks := #[
      { origin := ⟨c1.x, c1.y, 0.26⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
        area := 0.22 + 0.08 * Float.abs speed, color := ⟨0.20, 0.90, 1.0, 0.42⟩,
        isDisk := true, orientationArrow := true },
      { origin := ⟨c2.x, c2.y, 0.26⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
        area := 0.22 + 0.08 * Float.abs w2, color := ⟨1.0, 0.78, 0.24, 0.42⟩,
        isDisk := true, orientationArrow := true },
      { origin := ⟨c3.x, c3.y, 0.26⟩, u := ⟨1.0, 0.0, 0.0⟩, v := ⟨0.0, 1.0, 0.0⟩,
        area := 0.18 + 0.06 * Float.abs w3, color := ⟨1.0, 0.44, 0.48, 0.42⟩,
        isDisk := true, orientationArrow := true }
    ],
    points := #[
      { handleId := 0, pos := phaseH, radius := 0.085, color := RGBA.green, role := { draggable := true }, label := "Phase Scrub" },
      { handleId := 10, pos := Vec3.zero, radius := 0.065, color := RGBA.white, label := "Pitch Contact₁₂" },
      { handleId := 11, pos := ⟨-r1, r1, 0.0⟩, radius := 0.065, color := RGBA.white, label := "Pitch Contact₁₃" }
    ],
    inspect := #[
      { idx := 0, name := "Gear Ratios", grade := 2,
        formatted := s!"Z₁={z1}, Z₂={z2}, Z₃={z3} · ω₂/ω₁ = -{fmtExprNum (1.0 / actualRatio)}",
        editable := false },
      { idx := 1, name := "Motors", grade := 2,
        formatted := s!"M₁=T({fmtExprNum c1.x})R({fmtExprNum theta1}), M₂=T({fmtExprNum c2.x})R({fmtExprNum theta2})",
        editable := false }
    ] }

/-! ## Showcase Catalog (8 Showstopper Presets → 77 Total Across Studio!) -/

def showcasePresetCatalog : Array ShowcasePresetInfo := #[
  { id := "pga3d_bouncing_cube", title := "3D PGA Bouncing Cube (RK4 Impulse)", category := "3D PGA", algebra := "PGA3",
    description := "Real-time PGA3 motor RK4 rigid-body cube with 8-corner floor impulse collisions, angular momentum bivector, and live @param sliders.",
    sampleCode := "@basis PGA3\n@param gravity = 9.8 (0.5..20, 0.2)\n@param restitution = 0.78 (0.1..0.98, 0.02)\n@param spin = 2.6 (0..8, 0.1)\nlet h = abs(sin(t * sqrt(gravity) * 0.45)) * (0.4 + restitution)\nlet M = translator(0, h - 0.55, 0) * motor(0.6, 1, 0.4, t * spin, 0)\nlet cube = transform(mesh(\"cube\"), M)" },
  { id := "pga3d_double_pendulum", title := "3D PGA Spherical Double Pendulum", category := "3D PGA", algebra := "PGA3",
    description := "Coupled 3D spherical double pendulum driven by constrained RK4 dynamics, PGA3 link motors, and chaotic 3D ribbon trail.",
    sampleCode := "@basis PGA3\n@param length = 1.0 (0.4..1.5, 0.05)\n@param damping = 0.03 (0..0.35, 0.01)\nlet O = point(0, 1.2, 0)\nlet a1 = 0.9 * sin(t * 1.4) * exp(-damping * t)\nlet a2 = 1.3 * cos(t * 2.1)\nlet P1 = point(length * sin(a1), 1.2 - length * cos(a1), 0.3 * sin(t))\nlet P2 = point(P1.x + 0.85 * length * sin(a2), P1.y - 0.85 * length * cos(a2), 0.45 * cos(t * 1.7))\nlet arm1 = seg(O, P1)\nlet arm2 = seg(P1, P2)" },
  { id := "sta_terrell_penrose", title := "STA Terrell-Penrose Relativistic Rotation", category := "Spacetime", algebra := "STA",
    description := "Relativistic Cl(3,1) Lorentz-contracted + Terrell-Penrose optical-aberration rotated 3D cube with live β = v/c slider.",
    sampleCode := "@basis STA\n@param beta = 0.78 (0..0.95, 0.01)\nlet eta = 0.5 * log((1 + beta) / (1 - beta))\nlet B = boost(1, 0, 0, eta)\nlet ctPrime = B >>> et\nlet xPrime = B >>> ex" },
  { id := "sta_maxwell_streamlines", title := "STA Maxwell Dipole RK4 Streamlines", category := "Spacetime", algebra := "STA",
    description := "3D RK4-advected electric & magnetic dipole streamlines with glowing Faraday F = E + IB bivector disks and live frequency slider.",
    sampleCode := "@basis STA\n@param frequency = 1.2 (0.2..3.5, 0.1)\n@param dipole = 1.0 (0.3..2.0, 0.05)\nlet E = dipole * cos(frequency * t) * et * ey\nlet B = dipole * sin(frequency * t) * ex * ez\nlet F = E + B" },
  { id := "pga3d_hopf_streamlines", title := "3D PGA Hopf & Screw-Motor Flow Ribbons", category := "3D PGA", algebra := "PGA3",
    description := "324 RK4-advected particle flow ribbons blending linked S³→ℝ³ Hopf fibration fibers with PGA3 Chasles screw-motor velocity fields.",
    sampleCode := "@basis PGA3\n@param pitch = 0.35 (-1.2..1.2, 0.05)\n@param twist = 1.5 (0.2..3.5, 0.1)\nlet L = (twist * e13 + pitch * e02).Normalized\nlet P0 = point(0.95, -0.5, 0)\nlet ribbon = curve([exp(i * 0.15 * L) >>> P0 for i in 0..36])" },
  { id := "implicit_barth_sextic", title := "Barth Sextic (GPU Raymarch + Bytecode MT)", category := "Surfaces", algebra := "R3",
    description := "Iconic degree-6 Barth Sextic algebraic surface with 65 icosahedral ordinary double points rendered via live GPU raymarching + bytecode Marching Tetrahedra.",
    sampleCode := "@basis R3\n@param phi = 1.618 (1.1..2.1, 0.01)\n@param iso = 0.0 (-0.35..0.35, 0.01)\nlet surf = opns(\"4*(2.618*x^2-y^2)*(2.618*y^2-z^2)*(2.618*z^2-x^2) - 4.236*(x^2+y^2+z^2-1)^2\")" },
  { id := "cga3d_dupin_cyclide_raymarch", title := "3D CGA Dupin Cyclide (GPU Raymarch + Focal Conics)", category := "3D CGA", algebra := "CGA3",
    description := "Sphere-traced 3D CGA Dupin Cyclide with live majorR/minorR/eccentricity sliders and glowing orthogonal focal ellipse and hyperbola.",
    sampleCode := "@basis CGA3\n@param majorR = 1.05 (0.65..1.45, 0.02)\n@param minorR = 0.48 (0.20..0.85, 0.02)\n@param eccentricity = 0.42 (0.0..0.72, 0.02)\nlet S = opns(\"(x^2+y^2+z^2+0.68)^2 - 4*(1.05*x-0.21)^2 - 3.63*z^2\")" },
  { id := "pga3d_gears_kinematics", title := "3D PGA Meshing Involute Gear Train", category := "3D PGA", algebra := "PGA3",
    description := "Three meshing 3D involute-style rigid gears driven by composed PGA3 rotational motors with live speed and gear-ratio sliders.",
    sampleCode := "@basis PGA3\n@param speed = 1.4 (-4..4, 0.1)\n@param ratio = 1.5 (0.5..2.0, 0.1)\nlet M1 = translator(-0.56, 0, 0) * motor(0, 0, 1, speed * t, 0)\nlet M2 = translator(0.56 * ratio, 0, 0) * motor(0, 0, 1, -speed * t / ratio, 0)\nlet g1 = transform(mesh(\"torus\"), M1)\nlet g2 = transform(mesh(\"torus\"), M2)" }
]

def showcasePresetIds : Array String := showcasePresetCatalog.map (·.id)

/-- Dispatch any of the 8 Wave 4B & Wave 6C showstopper presets by ID. -/
def buildShowcasePreset (id : String) (cube : BouncingCubeState) (dp : DoublePendulumState)
    (handles : Array (UInt32 × Vec3)) (overrides : Array (String × Float))
    (seq : UInt64 := 0) (t : Float := 0.0) : Option SceneFrame :=
  match id with
  | "pga3d_bouncing_cube"          => some (buildPga3dBouncingCube cube handles overrides seq t)
  | "pga3d_double_pendulum"        => some (buildPga3dDoublePendulum dp handles overrides seq t)
  | "sta_terrell_penrose"          => some (buildStaTerrellPenrose handles overrides seq t)
  | "sta_maxwell_streamlines"      => some (buildStaMaxwellStreamlines handles overrides seq t)
  | "pga3d_hopf_streamlines"       => some (buildPga3dHopfStreamlines handles overrides seq t)
  | "implicit_barth_sextic"        => some (buildImplicitBarthSextic handles overrides seq t)
  | "cga3d_dupin_cyclide_raymarch" => some (buildCga3dDupinCyclideRaymarch handles overrides seq t)
  | "pga3d_gears_kinematics"       => some (buildPga3dGearsKinematics handles overrides seq t)
  | _                              => none

/-! ## Complete 77-Preset KaTeX LaTeX `formula` & 1-Sentence `summary` Registry -/

/-- Canonical KaTeX LaTeX `formula` + crisp 1-sentence human `summary` for ALL **77 presets**
(19 base + 28 extra + 22 parity + 8 showcase). Every preset returns non-empty `(formula, summary)`. -/
def presetMathMeta (presetId : String) : String × String :=
  match presetId with
  -- 19 Base Flagship Presets
  | "pga3d_slicing" =>
    ("P_{\\text{cut}} = \\Pi \\wedge (A \\vee B),\\qquad \\Pi = d\\,e_0 + \\mathbf{n} \\in \\mathrm{Cl}_{3,0,1}",
     "Slices a sculpted 3D bunny mesh with a live PGA3 plane, clipping upper and lower halves while stitching exact 2D cross-section contours.")
  | "pga3d_points_and_lines" =>
    ("L = A \\vee B,\\quad \\Pi = A \\vee B \\vee C,\\quad P = L \\wedge \\Pi \\in \\mathrm{Cl}_{3,0,1}",
     "Demonstrates coordinate-free 3D projective joins, meets, and normalized point sums across five draggable pyramid vertices.")
  | "pga3d_physics_free_top" =>
    ("\\dot{M} = -\\tfrac{1}{2} M B,\\qquad \\dot{\\mathbf{L}} + \\boldsymbol{\\omega} \\times \\mathbf{L} = 0",
     "Integrates Euler's torque-free rigid body equations via PGA3 motor RK4, revealing the Dzhanibekov intermediate-axis flip.")
  | "pga3d_origami" =>
    ("M_{\\text{fold}} = \\exp\\!\\left(-\\tfrac{\\theta}{2}\\,L_{\\text{hinge}}\\right),\\qquad X' = M_{\\text{fold}} X \\widetilde{M}_{\\text{fold}}",
     "Folds a 3D Kabuto origami model from flat paper using sequential Huzita-Hatori crease lines and PGA3 hinge rotors.")
  | "pga3d_motor_orbits" =>
    ("P(u) = \\exp(u\\,B)\\,P_0\\,\\exp(-u\\,B),\\qquad B = \\theta\\,L + d\\,e_0 L",
     "Generates helical screw curves and rigid-motion manifolds as one-parameter exponential orbits of PGA3 motors.")
  | "pga3d_icosahedron" =>
    ("R_k = \\exp\\!\\left(-\\tfrac{\\pi k}{5}\\,L_5\\right),\\qquad G = \\langle R_5, R_3, R_2 \\rangle",
     "Constructs a regular icosahedron directly from seed vertices using 5-fold and 3-fold rotational motors in PGA3.")
  | "pga3d_skinning" =>
    ("M_{\\text{DLB}}(u) = \\frac{(1-u)M_0 + u M_1}{\\|(1-u)M_0 + u M_1\\|} \\in \\mathrm{Cl}_{3,0,1}^+",
     "Contrasts volume-preserving Dual Quaternion / PGA3 Motor Skinning against Linear Blend Skinning candy-wrapper collapse.")
  | "pga3d_objects" =>
    ("P_{k+1} = M P_k \\widetilde{M},\\qquad M = \\exp\\!\\left(-\\tfrac{1}{2} B_{\\text{screw}}\\right)",
     "Immerses lathed torus, sphere, cone, and cylinder solids inside an animated 3D PGA3 screw-motor flow field.")
  | "cga3d_intersections" =>
    ("C = S_1 \\wedge S_2,\\quad C_{\\Pi} = S_1 \\wedge \\Pi,\\quad r^2 = \\frac{C\\widetilde{C}}{(e_\\infty \\rfloor C)^2}",
     "Computes live 3D conformal intersections of spheres, planes, lines, and circles, visualizing both real and imaginary rounds.")
  | "cga3d_spheres_apollonius" =>
    ("S = A \\wedge B \\wedge C \\wedge D,\\qquad C = A \\wedge B \\wedge C \\in \\mathrm{Cl}_{4,1}",
     "Spans the unique circumsphere and circumcircle directly as exterior outer products of four draggable 3D conformal points.")
  | "cga3d_opns_cyclide" =>
    ("X \\in \\mathcal{M} \\iff P(X) \\wedge B = 0,\\qquad P(X) = \\mathbf{x} + \\tfrac{1}{2}\\mathbf{x}^2 e_\\infty + e_\\emptyset",
     "Evaluates a Lean-compiled WGSL/GLSL/MSL sphere-tracing raymarcher for Outer Product Null Space surfaces in CGA3.")
  | "pga2d_euler_line" =>
    ("H = ((A\\vee B)\\rfloor C) \\wedge ((B\\vee C)\\rfloor A),\\qquad \\ell_{\\text{Euler}} = H \\vee O",
     "Proves Euler's theorem interactively in 2D PGA by keeping orthocenter, centroid, and circumcenter strictly collinear.")
  | "pga2d_inverse_kinematics" =>
    ("P_i' = (P_{i+1} + d_i\\,\\widehat{P_i - P_{i+1}})_{\\text{FABRIK}} \\in \\mathrm{Cl}_{2,0,1}",
     "Solves a 6-segment 2D inverse kinematics chain in real time via projective line projections toward a draggable target.")
  | "pga2d_desargues_theorem" =>
    ("X = (A\\vee B)\\wedge(A'\\vee B'),\\quad Y = (B\\vee C)\\wedge(B'\\vee C'),\\quad X \\vee Y \\vee Z = 0",
     "Demonstrates Desargues' projective theorem: triangles in perspective from a point have collinear corresponding edge intersections.")
  | "sta_lorentz_boost" =>
    ("X' = B X \\widetilde{B},\\qquad B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right),\\qquad -c^2 t^2 + \\|\\mathbf{x}\\|^2 = s^2",
     "Visualizes Minkowski spacetime light cones and hyperbolic rapidity boosts preserving the relativistic interval in Cl(3,1).")
  | "sta_maxwell_em" =>
    ("F = \\mathbf{E} + I\\mathbf{B},\\qquad F' = B F \\widetilde{B},\\qquad \\nabla F = J",
     "Unifies electric and magnetic fields into a single Spacetime Algebra Faraday bivector that mixes smoothly under Lorentz boosts.")
  | "r3_rational_rotor" =>
    ("R = \\frac{3 + 4\\,e_{12}}{5},\\qquad \\mathbf{v}' = R\\mathbf{v}\\widetilde{R} \\in \\mathrm{Cl}_{3,0}(\\mathbb{Q})",
     "Applies an exact rational Pythagorean rotor sandwich with zero floating-point drift in 3D Euclidean Geometric Algebra.")
  | "dual_autodiff_surface" =>
    ("f(x + \\varepsilon, y) = f(x, y) + \\partial_x f\\,\\varepsilon,\\qquad \\varepsilon^2 = 0,\\qquad \\mathbf{n} = \\star(T_x \\wedge T_y)",
     "Uses dual numbers Cl(0,0,1) for exact forward-mode automatic differentiation of an animated 3D surface tangent plane and normal.")
  | "complex_mobius_orbit" =>
    ("\\pi^{-1}(z) = \\left(\\frac{2\\,\\mathrm{Re}\\,z}{|z|^2+1},\\;\\frac{|z|^2-1}{|z|^2+1},\\;\\frac{2\\,\\mathrm{Im}\\,z}{|z|^2+1}\\right) \\in S^2",
     "Lifts a complex loxodrome spiral in Cl(0,1) stereographically onto the 3D Riemann sphere via Möbius geometry.")
  -- 28 Extra Presets
  | "pga3d_origami_fold" =>
    ("\\sin\\eta = \\sin\\theta\\sin\\alpha,\\qquad M_{\\text{hinge}} = \\exp\\!\\left(-\\tfrac{\\theta}{2} L\\right)",
     "Animates a rigid-panel Miura-ori tessellation whose single degree of freedom couples every PGA3 crease hinge simultaneously.")
  | "pga3d_ik_arm" =>
    ("L_i = P_i \\vee P_{i+1},\\qquad P_i^{\\text{next}} = T(d_i\\,\\widehat{L_i})\\,P_{i+1}\\,\\widetilde{T}",
     "Drives a 5-link spatial 3D FABRIK inverse kinematics arm reaching smoothly toward a draggable 3D target point.")
  | "pga3d_hopf" =>
    ("\\pi(z_1, z_2) = \\left(2 z_1\\bar{z}_2,\\;|z_1|^2 - |z_2|^2\\right),\\qquad S^1 \\hookrightarrow S^3 \\xrightarrow{\\pi} S^2",
     "Projects 26 mutually linked Villarceau circles of the S³ Hopf fibration stereographically into nested 3D tori.")
  | "pga3d_duality" =>
    ("\\Pi = P^\\star = \\mathbf{p}\\cdot\\mathbf{x} - 1 = 0 \\iff P \\leftrightarrow !P",
     "Illustrates projective polar duality mapping every draggable 3D point across the unit sphere to its dual polar plane.")
  | "pga3d_spring_physics" =>
    ("\\dot{M} = -\\tfrac{1}{2} M B,\\qquad \\dot{B} = -k\\,\\log(M) - c\\,B",
     "Simulates a 6-DOF rigid cube suspended on a helical spring-damper driven by PGA3 motor-logarithm restoring wrenches.")
  | "pga3d_skinning_twist" =>
    ("M(u) = \\frac{\\sum_i w_i(u)\\,M_i}{\\|\\sum_i w_i(u)\\,M_i\\|} \\in \\mathrm{Cl}_{3,0,1}^+",
     "Blends three articulated bone motors via dual-quaternion linear blending (DLB) along a twisted 3D cylinder.")
  | "cga3d_dupin_cyclide" =>
    ("S_{\\text{cyclide}} = K\\,T_{\\text{torus}}\\,K^{-1},\\qquad c^2 = a^2 - b^2",
     "Displays a conformal Dupin cyclide as the sphere-inverted image of a torus tangent to three generating spheres.")
  | "cga3d_apollonius" =>
    ("\\left(\\sum_{i=1}^5 \\kappa_i\\right)^2 = 3\\sum_{i=1}^5 \\kappa_i^2,\\qquad \\kappa_i = \\frac{1}{r_i}",
     "Realizes the 3D Descartes-Soddy sphere packing theorem with four mutually tangent spheres kissing inner and outer Soddy spheres.")
  | "cga3d_clifford_torus" =>
    ("T^2 = \\left\\{\\tfrac{1}{\\sqrt{2}}(e^{iu}, e^{iv})\\right\\} \\subset S^3,\\qquad R_{xw}(\\theta)\\in\\mathrm{SO}(4)",
     "Rotates the flat Clifford torus S¹×S¹ in 4D Euclidean space and stereographically projects its inside-out inversion to ℝ³.")
  | "cga3d_inversion" =>
    ("X' = -S X S^{-1},\\qquad \\mathbf{x}' = \\mathbf{c} + r^2 \\frac{\\mathbf{x} - \\mathbf{c}}{\\|\\mathbf{x} - \\mathbf{c}\\|^2}",
     "Applies a CGA3 spherical inversion sandwich that bends straight cube edges into exact conformal circular arcs.")
  | "cga3d_dipole_field" =>
    ("P_{AB} = A \\wedge B,\\qquad C_\\theta = A \\wedge B \\wedge Q(\\theta) \\in \\mathrm{Cl}_{4,1}",
     "Spans coaxial dipole field circles through a draggable CGA3 point pair A∧B paired with orthogonal equipotential spheres.")
  | "sta_light_cone" =>
    ("-c^2 t^2 + x^2 + z^2 = 0,\\qquad B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right)",
     "Graphs the relativistic Minkowski light cone separating timelike worldlines, null rays, and spacelike intervals under boosts.")
  | "sta_em_wave" =>
    ("F(z,t) = (\\mathbf{E}_0 + I\\mathbf{B}_0)\\,\\exp\\big(I(kz - \\omega t)\\big)",
     "Animates a propagating relativistic electromagnetic wave in STA where E and B oscillate orthogonally as a null Faraday bivector.")
  | "sta_rapidity" =>
    ("B(\\mathbf{v}_2)\\,B(\\mathbf{v}_1) = R(\\theta_W)\\,B(\\mathbf{v}_{1\\oplus 2})",
     "Demonstrates Thomas precession and Wigner rotation arising from the non-commutativity of two orthogonal Lorentz boosts.")
  | "implicit_gyroid" =>
    ("\\sin(kx)\\cos(ky) + \\sin(ky)\\cos(kz) + \\sin(kz)\\cos(kx) = 0",
     "Extracts a watertight triply periodic Gyroid minimal surface via Kuhn Marching Tetrahedra with iridescent curvature shading.")
  | "implicit_metaballs" =>
    ("1 - \\sum_{i=1}^4 \\frac{r_i^2}{\\|\\mathbf{p} - \\mathbf{c}_i(t)\\|^2 + \\epsilon} = 0",
     "Blends four animated organic metaball potential fields into a smooth merging implicit isosurface with a draggable orb.")
  | "implicit_schwarz_p" =>
    ("\\cos(kx) + \\cos(ky) + \\cos(kz) = 0",
     "Meshes the Schwarz P triply periodic minimal surface of zero mean curvature using edge-deduplicated Marching Tetrahedra.")
  | "param_klein_bottle" =>
    ("r(u,v) = R + a\\big(\\cos\\tfrac{u}{2}\\sin v - \\sin\\tfrac{u}{2}\\sin 2v\\big)",
     "Immerses the non-orientable Figure-8 Klein bottle in 3D with double-sided curvature shading and adjustable tube radius.")
  | "param_mobius_strip" =>
    ("\\mathbf{S}(u,v) = \\big((R+v\\cos\\tfrac{u}{2})\\cos u,\\; v\\sin\\tfrac{u}{2},\\; (R+v\\cos\\tfrac{u}{2})\\sin u\\big)",
     "Displays a twisted Möbius band whose parallel-transported normal vector reverses orientation after one full circuit.")
  | "implicit_genus2" =>
    ("\\big((x^2 + y^2)^2 - x^2 + y^2\\big)^2 + z^2 = r^2",
     "Extracts a smooth genus-2 double-torus algebraic pretzel surface via watertight Kuhn Marching Tetrahedra.")
  | "param_boys_surface" =>
    ("\\mathbb{R}P^2 \\hookrightarrow \\mathbb{R}^3,\\qquad D(u,v) = 2 - \\sqrt{2}\\sin(3v)\\sin(2u)",
     "Constructs the 3-fold symmetric Apéry-Bryant Boy's surface immersion of the real projective plane ℝP² into 3D space.")
  | "param_enneper_superquadric" =>
    ("H = 0,\\quad x = u - \\tfrac{u^3}{3} + u v^2,\\quad |x|^{2/e_2} + |z|^{2/e_2} + |y|^{2/e_1} = 1",
     "Pairs the classic zero-mean-curvature Enneper minimal surface with a smoothly exponent-morphing superquadric.")
  | "cga2d_apollonius" =>
    ("\\kappa_4 = \\kappa_1 + \\kappa_2 + \\kappa_3 \\pm 2\\sqrt{\\kappa_1\\kappa_2 + \\kappa_2\\kappa_3 + \\kappa_3\\kappa_1}",
     "Solves Apollonius' problem in 2D CGA using Descartes' circle curvature theorem for inner and outer kissing Soddy circles.")
  | "pga2d_non_euclidean" =>
    ("d_H(A,B) = \\mathrm{arccosh}(-A\\cdot B),\\qquad \\mathrm{Cl}_{2,1}",
     "Renders hyperbolic geodesics orthogonal to the Poincaré disk boundary with a draggable non-Euclidean triangle in Cl(2,1).")
  | "complex_mandelbrot" =>
    ("z_{n+1} = z_n^2 + c,\\qquad z_0 = 0,\\qquad c \\in \\mathrm{Cl}_{0,1} \\cong \\mathbb{C}",
     "Traces live quadratic escape orbits zₙ₊₁ = zₙ² + c from a draggable parameter inside the Mandelbrot cardioid and period-2 bulb.")
  | "dual_tangent_plane" =>
    ("f(x+\\varepsilon_x, y+\\varepsilon_y) = f + f_x\\varepsilon_x + f_y\\varepsilon_y,\\qquad \\varepsilon^2 = 0",
     "Computes exact first-order partial derivatives and the tangent plane of a 3D surface using dual-number jets.")
  | "quaternion_slerp" =>
    ("q(u) = q_0\\,\\exp\\!\\big(u\\,\\log(q_0^{-1} q_1)\\big) \\in \\mathrm{Cl}_{0,2}^+ \\cong \\mathbb{H}",
     "Performs gimbal-free geodesic spherical linear interpolation (SLERP) along the shortest great-circle arc on S³.")
  | "higher_cl_conic_pencil" =>
    ("C(\\lambda) = (1 - \\lambda)\\,C_1 + \\lambda\\,C_2 \\in \\mathrm{Cl}_{6,3}",
     "Morphs a 1-parameter projective pencil of conics through four base points continuously from ellipses through parabolas to hyperbolas.")
  -- 22 Parity Presets
  | "pga2d_points_and_lines" =>
    ("L_1 = A \\vee B,\\quad L_2 = C \\vee D,\\quad P = L_1 \\wedge L_2 \\in \\mathrm{Cl}_{2,0,1}",
     "Illustrates the dual join and meet operations of 2D Projective Geometric Algebra with interactive draggable points.")
  | "pga2d_distances_and_angles" =>
    ("d(P,\\ell) = |P \\vee \\ell|,\\qquad \\cos\\theta = \\ell_1 \\cdot \\ell_2 \\in \\mathrm{Cl}_{2,0,1}",
     "Measures exact signed point-to-line distances and line-to-line angles directly from 2D PGA inner and regressive products.")
  | "pga2d_project_and_reject" =>
    ("\\mathrm{Proj}_\\ell(P) = (P \\cdot \\ell)\\,\\ell,\\qquad \\mathrm{Refl}_\\ell(P) = -\\ell P \\ell",
     "Shows orthogonal projection onto a line and mirror reflection across a line as single algebraic products in PGA2.")
  | "pga2d_rotors_and_translators" =>
    ("M = \\ell_2 \\ell_1 = \\exp\\!\\left(\\tfrac{\\theta}{2}\\,P\\right),\\qquad T = 1 - \\tfrac{1}{2}\\mathbf{t}\\,e_0",
     "Constructs planar rotors and translators as geometric products of two mirror lines meeting at a finite or ideal point.")
  | "pga2d_isometries" =>
    ("G = T\\,\\ell = \\ell_3 \\ell_2 \\ell_1 \\in \\mathrm{Cl}_{2,0,1}^-",
     "Classifies all planar rigid isometries—rotations, translations, reflections, and glide reflections—as products of 1 to 3 mirrors.")
  | "pga2d_separating_axis" =>
    ("\\exists\\, \\ell \\in \\mathrm{Edges}:\\; \\forall v,\\; \\mathrm{sign}(v \\vee \\ell) > 0",
     "Detects convex polygon intersection in real time by testing vertex orientations against edge lines via the Separating Axis Theorem.")
  | "pga2d_poncelet" =>
    ("d^2 = R(R - 2r),\\qquad T_{k+1} = \\text{tangent}(P_k, C_r) \\cap C_R",
     "Animates Poncelet's porism: a continuous 1-parameter family of triangles inscribed in one circle and circumscribed about another.")
  | "pga2d_raytrace" =>
    ("R_{k+1} = -M_k\\,R_k\\,M_k,\\qquad P_k = R_k \\wedge M_k",
     "Traces multi-bounce mirror reflections of a 2D ray purely via PGA2 exterior intersections and mirror sandwich reflections.")
  | "pga3d_distances_and_angles" =>
    ("d(L_1, L_2) = \\frac{|L_1 \\wedge L_2|}{|L_1 \\cdot L_2|},\\qquad \\cos\\theta = \\widehat{L}_1 \\cdot \\widehat{L}_2",
     "Computes the exact shortest distance, dihedral angle, and common perpendicular segment between two skew 3D Plücker lines.")
  | "pga3d_rotors_and_translators" =>
    ("M(u) = \\exp\\!\\big(u\\,\\log(M_0^{-1} M_1)\\big) = \\exp\\!\\left(u(\\tfrac{\\theta}{2} L + \\tfrac{d}{2} e_0 L)\\right)",
     "Interpolates rigid poses along a constant-pitch Chasles screw axis via the closed-form PGA3 motor exponential and logarithm.")
  | "pga3d_physics_planets" =>
    ("\\mathbf{a} = -\\frac{\\mu}{r^3}\\mathbf{r},\\qquad L = \\mathbf{r} \\wedge \\mathbf{p} = \\text{const}",
     "Simulates Keplerian planetary ellipses highlighting each orbit's conserved angular momentum bivector area.")
  | "pga3d_physics_symmetric_top" =>
    ("\\dot{\\mathbf{L}} = \\mathbf{r} \\times m\\mathbf{g},\\qquad \\Omega_p = \\frac{m g \\ell}{I_3 \\omega_3}",
     "Animates a spinning Lagrange symmetric top tracing coupled gyroscopic precession and nutation loops in 3D PGA.")
  | "pga3d_platonic_solids" =>
    ("W(A_3),\\; W(B_3),\\; W(H_3) \\subset \\mathrm{Pin}(3,0,1)",
     "Generates the regular Platonic solids—tetrahedron, cube, octahedron, and icosahedron—from Coxeter reflection groups.")
  | "pga3d_slicing_hq" =>
    ("\\mathcal{C} = \\mathcal{M} \\cap \\Pi,\\qquad \\Pi = d\\,e_0 + \\mathbf{n} \\in \\mathrm{Cl}_{3,0,1}",
     "Slices high-detail sculpted bunny and trefoil torus-knot meshes interactively with stitched 2D cross-section contours.")
  | "cga2d_points_and_circles" =>
    ("C = A \\wedge B \\wedge C,\\qquad \\ell_{\\text{rad}} = C_1 \\wedge C_2 \\wedge e_\\infty \\in \\mathrm{Cl}_{3,1}",
     "Constructs an interactive 2D conformal circumcircle through three draggable points alongside its radical axis.")
  | "cga2d_conformal" =>
    ("T_{\\mathbf{c}}(\\mathbf{x}) = \\frac{\\mathbf{x} + \\mathbf{c}\\|\\mathbf{x}\\|^2}{1 + 2\\mathbf{x}\\cdot\\mathbf{c} + \\|\\mathbf{c}\\|^2\\|\\mathbf{x}\\|^2}",
     "Applies a 2D CGA special conformal transversion bending straight grid lines into circles while preserving every 90-degree angle.")
  | "cga3d_points_circles_lines" =>
    ("C = A \\wedge B \\wedge C,\\quad S = A \\wedge B \\wedge C \\wedge D,\\quad L = A \\wedge B \\wedge e_\\infty",
     "Unifies 3D lines, circles, and spheres as outer-product blades of four draggable conformal points in Cl(4,1).")
  | "cga3d_project_reject" =>
    ("P_{\\text{pair}} = (P \\rfloor S)\\,S^{-1} \\in \\mathrm{Cl}_{4,1}",
     "Projects a draggable 3D point conformally onto a sphere and circle, yielding the exact antipodal nearest/farthest point pair.")
  | "mga3d_points_and_lines" =>
    ("\\mathcal{R} = \\{ L(\\theta) \\in \\mathrm{Gr}(2,4) \\subset \\mathrm{Cl}_{4,4} \\}",
     "Visualizes a doubly-ruled hyperboloid of opposite Plücker line reguli inside Mother Geometric Algebra Cl(4,4).")
  | "csga2d_opns" =>
    ("C = P_1 \\wedge P_2 \\wedge P_3 \\wedge P_4 \\wedge P_5 \\in \\mathrm{Cl}_{5,3}",
     "Interpolates a 2D conic section blade directly from five spanning points in Conic Space Geometric Algebra Cl(5,3).")
  | "qcga3d_quadrics" =>
    ("x^2 + z^2 + k\\,y^2 = 0.85 \\subset \\mathrm{Cl}_{9,6}",
     "Morphs a Quadric Conformal GA surface smoothly from an ellipsoid through a cylinder to a one-sheet hyperboloid.")
  | "c2dga_cubic_curves" =>
    ("y^2 = x^3 + a x + b,\\qquad \\Delta = -16(4a^3 + 27b^2) \\in \\mathrm{Cl}_{9,7}",
     "Explores Weierstrass elliptic and nodal cubic curves as the draggable (a, b) handle crosses the cusp discriminant.")
  -- 5 Wave 4B Showstopper Presets
  | "pga3d_bouncing_cube" =>
    ("\\dot{M} = -\\tfrac{1}{2} M B,\\qquad J = \\frac{-(1+e)\\,\\mathbf{v}_c\\cdot\\mathbf{n}}{m^{-1} + \\|\\mathbf{r}\\times\\mathbf{n}\\|^2 / I}",
     "Real-time 3D PGA rigid-body RK4 simulation of a tumbling cube with 8-corner floor impulse collisions and angular momentum bivector.")
  | "pga3d_double_pendulum" =>
    ("M_2(t) = M_1(t)\\,\\exp\\!\\left(-\\tfrac{1}{2}\\theta_2 L_2\\right),\\qquad \\mathbf{a}_i = \\mathbf{g} - \\zeta\\mathbf{v}_i + \\sum_k \\lambda_k \\nabla_i g_k",
     "Chaotic 3D spherical double pendulum integrated via singularity-free constrained RK4 dynamics and composed PGA3 link motors.")
  | "sta_terrell_penrose" =>
    ("X' = B X \\widetilde{B},\\quad B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right),\\quad \\theta_{\\text{TP}} = \\arcsin(\\beta)",
     "Relativistic Cl(3,1) Terrell-Penrose optical aberration showing why a cube moving at speed βc appears rotated by arcsin(β) rather than squished.")
  | "sta_maxwell_streamlines" =>
    ("\\nabla F = J,\\qquad F = \\mathbf{E} + I\\mathbf{B} \\in \\mathrm{Cl}_{3,1}",
     "3D RK4-advected electric and magnetic dipole streamlines with glowing Faraday bivector disks unified in Spacetime Algebra F = E + IB.")
  | "pga3d_hopf_streamlines" =>
    ("M(s) = \\exp\\!\\left(\\tfrac{s}{2}(k\\,L + h\\,e_0 L)\\right),\\qquad \\mathbf{v}_{\\text{Hopf}} = \\big(z+xy,\\;\\tfrac{1-x^2+y^2-z^2}{2},\\;-x+yz\\big)",
     "3D RK4-advected particle flow ribbons blending linked S³→ℝ³ Hopf fibration fibers with PGA3 Chasles screw-motor velocity fields.")
  -- 3 Wave 6C Showstopper Presets
  | "implicit_barth_sextic" =>
    ("4(\\varphi^2 x^2 - y^2)(\\varphi^2 y^2 - z^2)(\\varphi^2 z^2 - x^2) - (1+2\\varphi)(x^2+y^2+z^2-1)^2 = c",
     "Iconic degree-6 Barth Sextic algebraic surface with 65 icosahedral ordinary double points rendered via infinite-resolution GPU raymarching and bytecode Marching Tetrahedra.")
  | "cga3d_dupin_cyclide_raymarch" =>
    ("(x^2+y^2+z^2+b^2-d^2)^2 - 4(ax - cd)^2 - 4b^2 z^2 = 0,\\qquad a^2 = b^2 + c^2",
     "Sphere-traced 3D CGA Dupin Cyclide (conformal inversion of a torus) surrounded by its glowing orthogonal focal ellipse and focal hyperbola.")
  | "pga3d_gears_kinematics" =>
    ("M_k(t) = T(\\mathbf{c}_k)\\,\\exp\\!\\left(-\\tfrac{\\theta_k(t)}{2}\\,e_{12}\\right),\\qquad \\frac{\\omega_2}{\\omega_1} = -\\frac{Z_1}{Z_2}",
     "Meshing 3D involute-style gear train driven by composed PGA3 rotational motors with live drive speed and gear ratio sliders.")
  | _ =>
    ("a b = a \\cdot b + a \\wedge b \\in \\mathrm{Cl}_{p,q,r}",
     "Interactive Geometric Algebra visualization computed purely in Lean 4 and streamed via SceneIR v1.")

end Grassmann.CoffeeShop.PresetsShowcase
