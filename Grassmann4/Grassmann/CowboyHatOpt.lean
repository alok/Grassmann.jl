/-
  Grassmann/CowboyHatOpt.lean - Cowboy Hat Shape Optimization

  Standalone module (no SciLean dependency).

  Models the cowboy hat as a surface of revolution Σ parameterized by arc length s ∈ [0, L].
  The profile angle ψ(s) fully determines the shape:
    r'(s) = cos ψ(s)    (radial increment)
    z'(s) = −sin ψ(s)   (height increment)

  At each surface point p ∈ Σ, the wind traction t(n) decomposes in Cl(3,0) as:
    t(n)·n = σ_N (scalar, normal stress) + B (bivector, shear/bending stress)

  Wind from +r direction: t(n) = p_wind · sin(ψ) · e_r
  Clifford product (analytically):
    t(n)·n = p·sin²(ψ) · 1  +  p·sin(ψ)·cos(ψ) · e₁₃
  so  σ_N = p·sin²(ψ),  |B| = (p/2)·|sin(2ψ)|

  The bivector part |B| is maximized at ψ = π/4 and zero at ψ ∈ {0, π/2}.
  The optimal brim transitions through intermediate angles, forcing |B| through
  a maximum at the gutter — exactly where the structural ridge forms.

  Optimization:
    min_ψ  F[ψ] = −λ_S·S + λ_W·W + λ_E·E + λ_M·M − λ_V·V
  subject to ψ(s) > 0 for s ∈ [s_c, L−δ] (rain runoff constraint).

  Solved by gradient descent with finite differences.
  Output: JSON animation sequence of optimization steps.
-/

namespace CowboyHatOpt

/-! ## Constants (standalone: no mathlib imports) -/

private def π    : Float := 3.14159265358979323846
private def π2   : Float := π / 2.0
private def twoπ : Float := 2.0 * π

@[inline] private def fabs (x : Float) : Float := if x < 0.0 then -x else x
@[inline] private def fmax (a b : Float) : Float := if a ≥ b then a else b
@[inline] private def fmin (a b : Float) : Float := if a ≤ b then a else b

/-! ## Hat Configuration -/

/-- All parameters controlling the hat geometry and optimization. -/
structure HatParams where
  /-- Number of arc-length sample points -/
  n          : Nat   := 80
  /-- Total arc length [m] -/
  L          : Float := 0.40
  /-- Index where brim begins (crown = 0..crownEnd-1, brim = crownEnd..n-1) -/
  crownEnd   : Nat   := 30
  /-- Target head radius at crown-brim junction [m] -/
  rHead      : Float := 0.090
  /-- Crown tip radius (nonzero to avoid singularity in H = sin(ψ)/r) -/
  r0         : Float := 0.010
  /-- Sun shading weight (maximize shadow area) -/
  lambdaS    : Float := 1.0
  /-- Wind drag weight (minimize frontal area) -/
  lambdaW    : Float := 0.35
  /-- Willmore energy weight (minimize bending cost) -/
  lambdaE    : Float := 0.55
  /-- Weight / areal density (minimize surface area) -/
  lambdaM    : Float := 0.25
  /-- Ventilation weight (maximize crown air volume) -/
  lambdaV    : Float := 0.75
  /-- Gradient descent learning rate -/
  lr         : Float := 0.008
  /-- Total optimization steps -/
  numSteps   : Nat   := 300
  /-- Save a frame every N steps -/
  frameEvery : Nat   := 10
  /-- Wind pressure magnitude [normalized] -/
  pWind      : Float := 1.0
  /-- Areal density [normalized] -/
  rho        : Float := 1.0

/-- Default: classic cattleman cowboy hat weights -/
def defaultParams : HatParams := {}

/-- Working-cowboy weights: more shade + ventilation, aerodynamic -/
def workingParams : HatParams :=
  { lambdaS := 1.5, lambdaV := 1.2, lambdaW := 0.5, lambdaE := 0.4, lambdaM := 0.2 }

/-- Dress-hat weights: stiffer material, tighter curl, lighter -/
def dressParams : HatParams :=
  { lambdaS := 0.7, lambdaV := 0.3, lambdaW := 0.3, lambdaE := 0.8, lambdaM := 0.5 }

/-! ## Geometric Types -/

/-- Per-point geometry derived from the ψ profile. -/
structure PointGeometry where
  s      : Float   -- arc length position
  psi    : Float   -- profile angle ψ(s)
  r      : Float   -- radius r(s)
  z      : Float   -- height z(s)
  H      : Float   -- mean curvature H(s)
  kappa  : Float   -- meridional curvature κ = dψ/ds
  deriving Inhabited

/-- Cl(3,0) stress decomposition at one surface point.

    Wind traction t(n) = p_wind · sin(ψ) · e_r  (wind from +r, axisymmetric)
    Normal n = sin(ψ)·e₁ + cos(ψ)·e₃

    Clifford product in Cl(3,0):
      t(n)·n = p·sin²(ψ) · 1  +  p·sin(ψ)cos(ψ) · e₁₃

    σ_N = scalar part (normal stress; how much force presses into surface)
    B   = bivector part magnitude (tangential/bending stress; how much shear force)

    Interpretation: at ψ = π/4 (45° brim), bending stress |B| is maximized.
    The optimal curl minimizes max |B| across the brim by distributing it uniformly.
-/
structure PointStress where
  sigmaN    : Float   -- normal stress σ_N = p·sin²ψ
  Bnorm     : Float   -- bivector norm |B| = (p/2)|sin 2ψ|
  normSq    : Float   -- Clifford norm² = σ_N² + |B|²

/-- All five functionals for a given hat shape. -/
structure Functionals where
  S        : Float   -- sun shading (want large)
  E        : Float   -- Willmore bending energy (want small)
  W        : Float   -- wind drag (want small)
  V        : Float   -- ventilation volume (want large)
  M        : Float   -- weight / surface area (want small)
  combined : Float   -- F[ψ] = −λ_S·S + λ_W·W + λ_E·E + λ_M·M − λ_V·V

/-- One captured frame of the animation sequence. -/
structure HatFrame where
  step  : Nat
  geom  : Array PointGeometry
  stress: Array PointStress
  funcs : Functionals

/-! ## Geometry Computation -/

/-- Compute full geometry (r, z, H, κ) from the ψ profile by forward integration. -/
def computeGeometry (params : HatParams) (psi : Array Float) : Array PointGeometry := Id.run do
  let n  := params.n
  let ds := params.L / Float.ofNat (n - 1)
  let mut geom : Array PointGeometry := #[]
  let mut r := params.r0
  let mut z := 0.15   -- crown tip starts at 15 cm above brim plane
  for i in List.range n do
    let p : Float := psi[i]!
    -- Meridional curvature dψ/ds by finite differences
    let kap : Float :=
      if i == 0 then
        (psi[1]! - psi[0]!) / ds
      else if i == n - 1 then
        (psi[n - 1]! - psi[n - 2]!) / ds
      else
        (psi[i + 1]! - psi[i - 1]!) / (2.0 * ds)
    -- Mean curvature H = (1/2)(dψ/ds + sin(ψ)/r)
    let azim : Float := if r > 1.0e-7 then Float.sin p / r else 0.0
    let H    : Float := 0.5 * (kap + azim)
    geom := geom.push { s := Float.ofNat i * ds, psi := p, r, z, H, kappa := kap }
    -- Forward Euler: r += cos(ψ)·ds, z -= sin(ψ)·ds
    if i < n - 1 then
      r := r + Float.cos p * ds
      z := z - Float.sin p * ds
  return geom

/-! ## Clifford Stress Computation -/

/-- Compute Cl(3,0) traction decomposition at each surface point.

    The wind blows in the −e_r direction (headwind in cylindrical coords).
    At a point with outward normal n = sin(ψ)·e₁ + cos(ψ)·e₃,
    the aerodynamic pressure traction is t(n) = p·sin(ψ)·e₁.

    Clifford product t(n)·n in Cl(3,0) = ℝ(e₁,e₂,e₃ | e_i² = +1):
      t(n)·n = p·sin(ψ)·e₁ · (sin(ψ)·e₁ + cos(ψ)·e₃)
             = p·sin²(ψ)·(e₁·e₁) + p·sin(ψ)cos(ψ)·(e₁·e₃)
             = p·sin²(ψ)·1  +  p·sin(ψ)cos(ψ)·e₁₃

    Grade-0 (scalar): σ_N = p·sin²(ψ)     — normal stress
    Grade-2 (bivector): B = p·sin(ψ)cos(ψ)·e₁₃  — shear/bending moment
    |B| = (p/2)|sin(2ψ)| — peaks at ψ = π/4, vanishes at ψ ∈ {0, π/2}
-/
def computeStress (params : HatParams) (geom : Array PointGeometry) : Array PointStress :=
  geom.map fun g =>
    let p    := params.pWind
    let sn   := Float.sin g.psi
    let cs   := Float.cos g.psi
    let sigN := p * sn * sn
    let bN   := (p / 2.0) * fabs (2.0 * sn * cs)
    { sigmaN := sigN, Bnorm := bN, normSq := sigN * sigN + bN * bN }

/-! ## Functionals -/

/-- Evaluate all five functionals from a precomputed geometry. -/
def computeFunctionals (params : HatParams) (geom : Array PointGeometry) : Functionals := Id.run do
  let n  := params.n
  let ds := params.L / Float.ofNat (n - 1)
  let mut E    := 0.0
  let mut W    := 0.0
  let mut M    := 0.0
  let mut V    := 0.0
  let mut rMax := 0.0
  for i in List.range n do
    let g : PointGeometry := geom[i]!
    E    := E + g.r * g.H * g.H * ds
    W    := W + twoπ * g.r * (Float.sin g.psi) ^ 2 * ds
    M    := M + g.r * ds
    if i < params.crownEnd then
      V  := V + g.r * g.r * Float.sin g.psi * ds
    rMax := fmax rMax g.r
  E := π * E
  M := twoπ * params.rho * M
  V := π * V
  -- Sun shading: time-averaged shadow area S ≈ π·r_max² (maximize brim radius)
  let S := π * rMax * rMax
  let combined :=
    -(params.lambdaS * S) + params.lambdaW * W + params.lambdaE * E
    + params.lambdaM * M - params.lambdaV * V
  return { S, E, W, V, M, combined }

/-! ## Initialization -/

/-- Initialize ψ to a classic cowboy-hat profile:
    Crown (0..crownEnd−1): ψ = 0 at dome top → π/2 at side wall (hemispherical)
    Brim (crownEnd..n−1): ψ drops from π/4 with a cubic curl at the edge.

    Geometry: r grows ≈ (2s_c/π) over the crown, reaching r ≈ r_head. -/
def initializeHat (params : HatParams) : Array Float :=
  let n  := params.n
  let ce := params.crownEnd
  Array.range n |>.map fun i =>
    if i < ce then
      -- Crown: linear ramp 0 → π/2 (hemispherical profile)
      π2 * Float.ofNat i / Float.ofNat ce
    else
      -- Brim: π/4 slope, smoothly transitioning to edge curl
      let t := Float.ofNat (i - ce) / Float.ofNat (n - 1 - ce)
      (π2 / 2.0) * (1.0 - t)          -- main brim slope (π/4 → 0)
      - (π / 12.0) * t * t * t        -- edge curl (cubic onset, −15° at edge)

/-! ## Gradient Descent -/

/-- Compute gradient of F via forward finite differences.
    ∂F/∂ψ_i ≈ (F(ψ + ε·eᵢ) − F(ψ)) / ε
    Coupling: changing ψ[i] affects r[j] for all j > i via integration. -/
def computeGradient (params : HatParams) (psi : Array Float) : Array Float :=
  let eps   := 1.0e-5
  let baseG := computeGeometry params psi
  let baseF := (computeFunctionals params baseG).combined
  Array.range psi.size |>.map fun i =>
    -- Perturb only the i-th angle (explicit index to avoid Fin/Nat mismatch)
    let psiPlus := Array.range psi.size |>.map fun j => if j == i then psi[j]! + eps else psi[j]!
    let gPlus   := computeGeometry params psiPlus
    let fPlus   := (computeFunctionals params gPlus).combined
    (fPlus - baseF) / eps

/-- Project ψ to satisfy the rain runoff constraint: ψ > 0 in the brim interior.
    The edge strip (last `delta` points) is left free so it can curl up (ψ < 0). -/
def projectConstraints (params : HatParams) (psi : Array Float) : Array Float :=
  let n     := psi.size
  let delta := 5   -- free-edge strip (can curl up)
  Array.range n |>.map fun i =>
    let p := psi[i]!
    if i >= params.crownEnd && i < n - delta then
      fmax 0.005 p   -- enforce rain runoff: ψ > 0 in brim interior
    else
      p

/-- One gradient descent step with constraint projection. -/
def gradientStep (params : HatParams) (psi : Array Float) : Array Float :=
  let grad   := computeGradient params psi
  -- ψ ← ψ − lr·∇F  (manual map avoids Array.zipWith signature ambiguity)
  let newPsi := Array.range psi.size |>.map fun i => psi[i]! - params.lr * grad[i]!
  projectConstraints params newPsi

/-! ## Frame Capture -/

/-- Capture the current optimization state as a HatFrame. -/
def captureFrame (step : Nat) (psi : Array Float) (params : HatParams) : HatFrame :=
  let geom   := computeGeometry params psi
  let stress := computeStress params geom
  let funcs  := computeFunctionals params geom
  { step, geom, stress, funcs }

/-! ## JSON Serialization -/

private def jf (x : Float) : String := s!"{x}"

private def geomPtJson (g : PointGeometry) : String :=
  s!"\{\"s\":{jf g.s},\"r\":{jf g.r},\"z\":{jf g.z}," ++
  s!"\"psi\":{jf g.psi},\"H\":{jf g.H},\"kappa\":{jf g.kappa}}"

private def stressPtJson (st : PointStress) : String :=
  s!"\{\"sigmaN\":{jf st.sigmaN},\"Bnorm\":{jf st.Bnorm},\"normSq\":{jf st.normSq}}"

private def funcsJson (f : Functionals) : String :=
  s!"\{\"S\":{jf f.S},\"E\":{jf f.E},\"W\":{jf f.W}," ++
  s!"\"V\":{jf f.V},\"M\":{jf f.M},\"combined\":{jf f.combined}}"

/-- Serialize one frame to compact JSON. -/
def frameJson (frame : HatFrame) : String :=
  let geomArr   := "[" ++ String.intercalate "," (frame.geom.toList.map geomPtJson) ++ "]"
  let stressArr := "[" ++ String.intercalate "," (frame.stress.toList.map stressPtJson) ++ "]"
  s!"\{\"step\":{frame.step},\"functionals\":{funcsJson frame.funcs}," ++
  s!"\"geometry\":{geomArr},\"stress\":{stressArr}}"

/-- Serialize the full animation to JSON. -/
def animationJson (params : HatParams) (frames : Array HatFrame) : String :=
  let metaStr :=
    s!"\{\"n\":{params.n},\"L\":{jf params.L},\"crownEnd\":{params.crownEnd}," ++
    s!"\"rHead\":{jf params.rHead},\"r0\":{jf params.r0}}"
  let lams :=
    s!"\{\"S\":{jf params.lambdaS},\"W\":{jf params.lambdaW},\"E\":{jf params.lambdaE}," ++
    s!"\"M\":{jf params.lambdaM},\"V\":{jf params.lambdaV}}"
  let framesArr := "[" ++ String.intercalate "," (frames.toList.map frameJson) ++ "]"
  s!"\{\"metadata\":{metaStr},\"lambdas\":{lams},\"frames\":{framesArr}}"

/-! ## Main Optimization Loop -/

/-- Run the full optimization and return all collected frames. -/
def runOptimization (params : HatParams) : IO (Array HatFrame) := do
  IO.eprintln s!"CowboyHatOpt: n={params.n}, L={params.L}m, {params.numSteps} steps"
  IO.eprintln s!"  λ=(S={params.lambdaS}, W={params.lambdaW}, E={params.lambdaE}, M={params.lambdaM}, V={params.lambdaV})"
  let mut psi    := initializeHat params
  let mut frames : Array HatFrame := #[]
  for step in List.range params.numSteps do
    if step % params.frameEvery == 0 then
      let fr := captureFrame step psi params
      frames := frames.push fr
      IO.eprintln s!"  step={step}  F={jf fr.funcs.combined}  E={jf fr.funcs.E}  V={jf fr.funcs.V}"
    psi := gradientStep params psi
  let final := captureFrame params.numSteps psi params
  frames := frames.push final
  IO.eprintln s!"Done. {frames.size} frames, final F={jf final.funcs.combined}"
  return frames

end CowboyHatOpt
