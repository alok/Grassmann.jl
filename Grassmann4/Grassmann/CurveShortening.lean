/-
  Grassmann/CurveShortening.lean - Curve Shortening Flow using Geometric Algebra

  Curve shortening flow is a geometric evolution where each point on a curve
  moves in the direction of its curvature vector with speed proportional to
  the curvature magnitude:

    ∂γ/∂t = κN

  where κ is the curvature and N is the unit normal.

  This implementation uses Grassmann's geometric algebra primitives:
  - Vectors as grade-1 multivectors (MV R2 .odd)
  - Normal computed via pseudoscalar: N = T * I (rotate tangent by 90°)
  - Curvature approximated by discrete Laplacian

  Key GA insight: Rotation by 90° is multiplication by the pseudoscalar I = e₁₂:
    v * I rotates v counter-clockwise by 90°
    I * v rotates v clockwise by 90°
-/
import Grassmann.MV

namespace Grassmann.CurveShortening

open Grassmann

/-! ## Float utilities -/

def Float.pi : Float := 3.14159265358979323846
def Float.inf : Float := 1.0 / 0.0
@[inline] def Float.min (a b : Float) : Float := if a ≤ b then a else b
@[inline] def Float.max (a b : Float) : Float := if a ≥ b then a else b

/-! ## 2D Geometric Algebra using MV

We use MV R2 .odd for vectors (grade-1 elements have odd parity).
In 2D R2:
- e₁ has blade mask 1 (binary 01)
- e₂ has blade mask 2 (binary 10)
- e₁₂ has blade mask 3 (binary 11), which is even parity (grade 2) -/

/-- Create a 2D vector from components using MV.
    For .odd parity in 2D, we have 2 packed coefficients. -/
@[inline]
def vec2 (x y : Float) : MV R2 .odd :=
  let m := MV.zero R2 .odd
  let m := m.setCoeff 1 x  -- e₁ at mask 1
  m.setCoeff 2 y           -- e₂ at mask 2

/-- Get x component of a 2D vector (e₁ coefficient) -/
@[inline]
def getX (v : MV R2 .odd) : Float := v.coeff 1

/-- Get y component of a 2D vector (e₂ coefficient) -/
@[inline]
def getY (v : MV R2 .odd) : Float := v.coeff 2

/-- Add two vectors -/
@[inline]
def vadd (a b : MV R2 .odd) : MV R2 .odd := MV.add a b

/-- Subtract vectors -/
@[inline]
def vsub (a b : MV R2 .odd) : MV R2 .odd := MV.sub a b

/-- Scale vector -/
@[inline]
def vsmul (s : Float) (v : MV R2 .odd) : MV R2 .odd := MV.smul s v

/-- Rotate vector 90° counter-clockwise (conceptually: v * I)
    In 2D: (a·e₁ + b·e₂) * e₁₂ = -b·e₁ + a·e₂ -/
@[inline]
def rotateCCW (v : MV R2 .odd) : MV R2 .odd :=
  let a := getX v
  let b := getY v
  vec2 (-b) a

/-- Rotate vector 90° clockwise (conceptually: I * v)
    In 2D: e₁₂ * (a·e₁ + b·e₂) = b·e₁ - a·e₂ -/
@[inline]
def rotateCW (v : MV R2 .odd) : MV R2 .odd :=
  let a := getX v
  let b := getY v
  vec2 b (-a)

/-- Dot product of two vectors: a · b = a₁b₁ + a₂b₂ -/
@[inline]
def dot2 (a b : MV R2 .odd) : Float :=
  getX a * getX b + getY a * getY b

/-- Squared norm -/
@[inline]
def normSq2 (v : MV R2 .odd) : Float := dot2 v v

/-- Norm (magnitude) -/
@[inline]
def norm2 (v : MV R2 .odd) : Float := Float.sqrt (normSq2 v)

/-- Normalize a vector -/
@[inline]
def normalize2 (v : MV R2 .odd) : MV R2 .odd :=
  let n := norm2 v
  if n > 1e-10 then vsmul (1.0 / n) v else MV.zero R2 .odd

/-- Cross product in 2D (returns scalar z-component) -/
@[inline]
def cross2 (a b : MV R2 .odd) : Float :=
  getX a * getY b - getY a * getX b

/-! ## Discrete Curve using MV Vectors

A closed curve represented as an array of 2D multivectors. -/

structure Curve where
  vertices : Array (MV R2 .odd)

-- Provide Inhabited instance for MV to enable array access with !
instance : Inhabited (MV R2 .odd) := ⟨MV.zero R2 .odd⟩

namespace Curve

/-- Number of vertices -/
@[inline] def numVertices (c : Curve) : Nat := c.vertices.size

/-- Get vertex with wrapping for closed curves -/
@[inline] def vertex (c : Curve) (i : Nat) : MV R2 .odd :=
  let n := c.numVertices
  if n = 0 then MV.zero R2 .odd
  else c.vertices[i % n]!

/-- Total arc length of the curve -/
def arcLength (c : Curve) : Float :=
  let n := c.numVertices
  (List.range n).foldl (init := 0.0) fun acc i =>
    let p0 := c.vertex i
    let p1 := c.vertex (i + 1)
    acc + norm2 (vsub p1 p0)

/-- Centroid (center of mass) of the curve vertices -/
def centroid (c : Curve) : MV R2 .odd :=
  let n := c.numVertices
  if n = 0 then MV.zero R2 .odd
  else
    let sum := c.vertices.foldl (init := MV.zero R2 .odd) vadd
    vsmul (1.0 / n.toFloat) sum

/-- Enclosed area using the wedge product (shoelace formula via GA)
    Area = ½ Σᵢ (pᵢ ∧ p_{i+1}) where ∧ extracts signed area -/
def signedArea (c : Curve) : Float :=
  let n := c.numVertices
  let sum := (List.range n).foldl (init := 0.0) fun acc i =>
    let p0 := c.vertex i
    let p1 := c.vertex (i + 1)
    acc + cross2 p0 p1
  sum / 2.0

/-- Absolute enclosed area -/
def area (c : Curve) : Float := Float.abs c.signedArea

/-! ## Curvature Computation using GA -/

/-- Discrete curvature vector at vertex i using the discrete Laplacian.
    κN ≈ (v_{i+1} - 2vᵢ + v_{i-1})

    This points toward the center of curvature with magnitude proportional
    to the curvature κ. -/
@[inline]
def curvatureVector (c : Curve) (i : Nat) : MV R2 .odd :=
  let n := c.numVertices
  if n < 3 then MV.zero R2 .odd
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    -- Discrete Laplacian: second derivative approximation
    vadd (vsub next (vsmul 2.0 curr)) prev

/-- Tangent vector at vertex i (unit vector along curve)
    T = normalize((v_{i+1} - v_{i-1}) / 2) -/
def tangent (c : Curve) (i : Nat) : MV R2 .odd :=
  let n := c.numVertices
  if n < 3 then MV.zero R2 .odd
  else
    let prev := c.vertex ((i + n - 1) % n)
    let next := c.vertex ((i + 1) % n)
    normalize2 (vsmul 0.5 (vsub next prev))

/-- Normal vector at vertex i using pseudoscalar rotation.
    N = T * I (rotate tangent CCW by 90°)

    This is the key GA insight: multiplication by the pseudoscalar
    rotates vectors in the plane. -/
def normal (c : Curve) (i : Nat) : MV R2 .odd :=
  rotateCCW (c.tangent i)

/-- Discrete curvature magnitude at vertex i.
    κ ≈ |curvature vector| / average edge length -/
def curvature (c : Curve) (i : Nat) : Float :=
  let n := c.numVertices
  if n < 3 then 0.0
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    let kVec := c.curvatureVector i
    let L := (norm2 (vsub curr prev) + norm2 (vsub next curr)) / 2.0
    if L > 1e-10 then norm2 kVec / L else 0.0

/-! ## Curve Shortening Flow -/

/-- One step of curve shortening flow with explicit Euler integration.

    v_i(t+Δt) = v_i(t) + Δt * κN_i

    where κN_i is the discrete curvature vector (Laplacian) at vertex i. -/
def step (c : Curve) (dt : Float) : Curve :=
  let n := c.numVertices
  let newVerts := (Array.range n).map fun i =>
    let v := c.vertex i
    let kVec := c.curvatureVector i
    vadd v (vsmul dt kVec)
  ⟨newVerts⟩

/-- Adaptive timestep based on minimum edge length.
    Uses Δt = α * min(L²) where α < 0.25 for stability. -/
def adaptiveTimestep (c : Curve) (alpha : Float := 0.1) : Float :=
  let n := c.numVertices
  if n < 2 then 0.01
  else
    let minLenSq := (List.range n).foldl (init := Float.inf) fun acc i =>
      let L := normSq2 (vsub (c.vertex (i + 1)) (c.vertex i))
      Float.min acc L
    alpha * minLenSq

/-- Run curve shortening for a given number of steps -/
def evolve (c : Curve) (steps : Nat) (dt : Float := 0.01) : Curve :=
  (List.range steps).foldl (init := c) fun curve _ => curve.step dt

/-! ## Curve Constructors using GA -/

/-- Create a regular n-gon centered at origin with given radius -/
def regularPolygon (n : Nat) (radius : Float := 1.0) (center : MV R2 .odd := MV.zero R2 .odd) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range n).map fun i =>
      let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
      vadd center (vec2 (radius * Float.cos θ) (radius * Float.sin θ))
    ⟨verts⟩

/-- Create an ellipse approximation -/
def ellipse (a b : Float) (n : Nat := 64) (center : MV R2 .odd := MV.zero R2 .odd) : Curve :=
  let verts := (Array.range n).map fun i =>
    let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
    vadd center (vec2 (a * Float.cos θ) (b * Float.sin θ))
  ⟨verts⟩

/-- Create a star-shaped curve -/
def star (n : Nat) (outerRadius innerRadius : Float) (center : MV R2 .odd := MV.zero R2 .odd) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range (2 * n)).map fun i =>
      let θ := Float.pi * i.toFloat / n.toFloat
      let r := if i % 2 = 0 then outerRadius else innerRadius
      vadd center (vec2 (r * Float.cos θ) (r * Float.sin θ))
    ⟨verts⟩

/-- Create a figure-8 (lemniscate-like) curve -/
def figure8 (scale : Float := 1.0) (n : Nat := 64) : Curve :=
  let verts := (Array.range n).map fun i =>
    let t := 2.0 * Float.pi * i.toFloat / n.toFloat
    let x := scale * Float.sin t
    let y := scale * Float.sin t * Float.cos t
    vec2 x y
  ⟨verts⟩

end Curve

/-! ## Visualization Helpers -/

/-- Convert curve to SVG path string -/
def curveToSVGPath (c : Curve) (scale : Float := 100.0) (offsetX offsetY : Float := 200.0) : String :=
  if c.numVertices = 0 then ""
  else
    let start := c.vertex 0
    let startStr := s!"M {offsetX + scale * getX start} {offsetY - scale * getY start}"
    let pathStr := (List.range (c.numVertices - 1)).foldl (init := startStr) fun acc i =>
      let p := c.vertex (i + 1)
      acc ++ s!" L {offsetX + scale * getX p} {offsetY - scale * getY p}"
    pathStr ++ " Z"

/-- Generate SVG showing curve evolution with rainbow colors -/
def evolutionSVG (initial : Curve) (steps : Nat) (dt : Float := 0.005)
    (everyNth : Nat := 50) : String :=
  let header := "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 400 400\">\n"
  let header := header ++ "  <rect width=\"400\" height=\"400\" fill=\"white\"/>\n"
  let rec go (c : Curve) (stepNum : Nat) (paths : String) (hue : Float) : String :=
    if stepNum >= steps then paths
    else
      let newC := c.step dt
      let newPaths := if stepNum % everyNth = 0 then
        let color := s!"hsl({hue}, 70%, 50%)"
        let opacity := 1.0 - (stepNum.toFloat / steps.toFloat) * 0.7
        paths ++ s!"  <path d=\"{curveToSVGPath newC}\" fill=\"none\" \
                     stroke=\"{color}\" stroke-width=\"1\" opacity=\"{opacity}\"/>\n"
      else paths
      go newC (stepNum + 1) newPaths (hue + 360.0 / (steps.toFloat / everyNth.toFloat))
  termination_by steps - stepNum
  let initialPath := s!"  <path d=\"{curveToSVGPath initial}\" fill=\"none\" \
                         stroke=\"blue\" stroke-width=\"2\"/>\n"
  let allPaths := go initial 0 initialPath 0.0
  let footer := "</svg>"
  header ++ allPaths ++ footer

/-! ## Demo / Tests -/

section Demo

/-- Demo: Curve shortening on a square using MV vectors -/
def demoSquare : IO Unit := do
  let square := Curve.regularPolygon 4 1.5
  IO.println s!"Initial square (using MV R2 .odd):"
  IO.println s!"  Vertices: {square.numVertices}"
  IO.println s!"  Arc length: {square.arcLength}"
  IO.println s!"  Area: {square.area}"
  let evolved := square.evolve 100 0.01
  IO.println s!"\nAfter 100 steps of curve shortening flow:"
  IO.println s!"  Arc length: {evolved.arcLength}"
  IO.println s!"  Area: {evolved.area}"
  -- Check vertices are becoming more circular
  let cent := evolved.centroid
  let distances := evolved.vertices.map fun v => norm2 (vsub v cent)
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"
  IO.println s!"  (Approaches 1.0 as curve becomes circular)"

/-- Demo: Show tangent and normal computation using pseudoscalar -/
def demoTangentNormal : IO Unit := do
  IO.println s!"\n--- Tangent and Normal via Pseudoscalar ---"
  let circle := Curve.regularPolygon 8 1.0
  for i in [:4] do
    let T := circle.tangent i
    let N := circle.normal i  -- N = rotateCCW(T) = T * I conceptually
    IO.println s!"Vertex {i}: T = ({getX T}, {getY T}), N = ({getX N}, {getY N})"
    -- Verify N is perpendicular to T
    let dotTN := dot2 T N
    IO.println s!"  T·N = {dotTN} (should be ≈0)"

/-- Demo: Curve shortening on a star -/
def demoStar : IO Unit := do
  let star := Curve.star 5 1.5 0.5
  IO.println s!"\nInitial 5-pointed star:"
  IO.println s!"  Vertices: {star.numVertices}"
  IO.println s!"  Arc length: {star.arcLength}"
  IO.println s!"  Area: {star.area}"
  -- Evolve with adaptive timestep
  let mut curve := star
  for _ in [:200] do
    let dt := curve.adaptiveTimestep 0.08
    curve := curve.step dt
  IO.println s!"\nAfter 200 adaptive steps:"
  IO.println s!"  Arc length: {curve.arcLength}"
  IO.println s!"  Area: {curve.area}"
  let cent := curve.centroid
  let distances := curve.vertices.map fun v => norm2 (vsub v cent)
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"

/-- Run all demos -/
def runAllDemos : IO Unit := do
  IO.println "=== Curve Shortening Flow Demo (using Grassmann MV) ===\n"
  demoSquare
  demoTangentNormal
  demoStar
  IO.println "\n=== Demo Complete ==="

end Demo

/-! ## Extension to 3D and Surfaces

The GA formulation naturally extends to higher dimensions:

1. **3D Space Curves**: Use MV R3 .odd for vectors
   - Tangent T, Normal N, Binormal B form the Frenet frame
   - Curvature: κN ≈ d²γ/ds² = discrete Laplacian
   - Torsion: τB involves third derivatives

2. **Surface Mean Curvature Flow**: Use MV R3 .odd for mesh vertices
   - Each vertex moves by: v += dt * H * n
   - H = mean curvature = (κ₁ + κ₂)/2
   - Can be computed via cotangent Laplacian on mesh

The pseudoscalar multiplication extends naturally:
- In R3: I = e₁₂₃, and v * I gives the Hodge dual
- For surfaces: the normal n = (∂σ/∂u ∧ ∂σ/∂v) / |∂σ/∂u ∧ ∂σ/∂v|
-/

end Grassmann.CurveShortening
