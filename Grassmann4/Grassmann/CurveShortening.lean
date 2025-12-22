/-
  Grassmann/CurveShortening.lean - Curve Shortening Flow Demo

  Curve shortening flow is a geometric evolution where each point on a curve
  moves in the direction of its curvature vector with speed proportional to
  the curvature magnitude:

    ∂γ/∂t = κN

  where κ is the curvature and N is the unit normal.

  For a discrete curve (polygon), the mean curvature at vertex vᵢ is approximated
  by the discrete Laplacian:

    κN ≈ (v_{i+1} - 2vᵢ + v_{i-1}) / L

  This causes:
  - Convex regions to shrink inward
  - Concave regions to expand outward
  - The curve to become more circular over time
  - Eventually collapse to a "round point" (Grayson's theorem)

  This demo implements curve shortening on 2D curves using geometric algebra
  primitives for vector operations.
-/

namespace Grassmann.CurveShortening

/-! ## Float utilities (not in stdlib) -/

def Float.pi : Float := 3.14159265358979323846
def Float.inf : Float := 1.0 / 0.0
def Float.negInf : Float := -1.0 / 0.0

@[inline] def Float.min (a b : Float) : Float := if a ≤ b then a else b
@[inline] def Float.max (a b : Float) : Float := if a ≥ b then a else b

/-! ## 2D Vector Operations

Simple 2D vector type for curve representation.
Uses Float for compatibility with MV-based operations. -/

structure Vec2 where
  x : Float
  y : Float
  deriving Repr, BEq, Inhabited

namespace Vec2

@[inline] def zero : Vec2 := ⟨0.0, 0.0⟩

@[inline] def add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩

@[inline] def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩

@[inline] def scale (s : Float) (v : Vec2) : Vec2 := ⟨s * v.x, s * v.y⟩

@[inline] def scaleR (v : Vec2) (s : Float) : Vec2 := ⟨s * v.x, s * v.y⟩

@[inline] def dot (a b : Vec2) : Float := a.x * b.x + a.y * b.y

@[inline] def normSq (v : Vec2) : Float := v.dot v

@[inline] def norm (v : Vec2) : Float := Float.sqrt v.normSq

@[inline] def normalize (v : Vec2) : Vec2 :=
  let n := v.norm
  if n > 1e-10 then ⟨v.x / n, v.y / n⟩ else zero

/-- Cross product (returns scalar z-component in 2D) -/
@[inline] def cross (a b : Vec2) : Float := a.x * b.y - a.y * b.x

/-- Perpendicular vector (rotate 90° counter-clockwise) -/
@[inline] def perp (v : Vec2) : Vec2 := ⟨-v.y, v.x⟩

instance : Add Vec2 := ⟨add⟩
instance : Sub Vec2 := ⟨sub⟩
instance : Neg Vec2 := ⟨fun v => ⟨-v.x, -v.y⟩⟩
instance : HMul Float Vec2 Vec2 := ⟨scale⟩
instance : HMul Vec2 Float Vec2 := ⟨scaleR⟩

end Vec2

/-! ## Discrete Curve

A closed curve represented as an array of vertices. -/

structure Curve where
  vertices : Array Vec2
  deriving Repr

namespace Curve

/-- Number of vertices -/
@[inline] def numVertices (c : Curve) : Nat := c.vertices.size

/-- Get vertex with wrapping for closed curves -/
@[inline] def vertex (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n = 0 then Vec2.zero
  else c.vertices[i % n]!

/-- Get vertex with signed index (for i-1 style access) -/
@[inline] def vertexSigned (c : Curve) (i : Int) : Vec2 :=
  let n := c.numVertices
  if n = 0 then Vec2.zero
  else
    let idx := (i % n + n) % n
    c.vertices[idx.toNat]!

/-- Total arc length of the curve -/
def arcLength (c : Curve) : Float :=
  let n := c.numVertices
  (List.range n).foldl (init := 0.0) fun acc i =>
    let p0 := c.vertex i
    let p1 := c.vertex (i + 1)
    acc + (p1 - p0).norm

/-- Centroid (center of mass) of the curve vertices -/
def centroid (c : Curve) : Vec2 :=
  let n := c.numVertices
  if n = 0 then Vec2.zero
  else
    let sum := c.vertices.foldl (init := Vec2.zero) (· + ·)
    (1.0 / n.toFloat) * sum

/-- Enclosed area (signed, positive for counter-clockwise) using shoelace formula -/
def signedArea (c : Curve) : Float :=
  let n := c.numVertices
  let sum := (List.range n).foldl (init := 0.0) fun acc i =>
    let p0 := c.vertex i
    let p1 := c.vertex (i + 1)
    acc + p0.cross p1
  sum / 2.0

/-- Absolute enclosed area -/
def area (c : Curve) : Float := Float.abs c.signedArea

/-! ## Curvature Computation -/

/-- Discrete curvature vector at vertex i using the discrete Laplacian.
    κN ≈ (v_{i+1} - 2vᵢ + v_{i-1})

    This points toward the center of curvature with magnitude proportional
    to the curvature κ. -/
@[inline]
def curvatureVector (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n < 3 then Vec2.zero
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    next - (2.0 * curr) + prev

/-- Discrete curvature magnitude at vertex i.
    Approximated as |curvature vector| / average edge length. -/
def curvature (c : Curve) (i : Nat) : Float :=
  let n := c.numVertices
  if n < 3 then 0.0
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    let kVec := c.curvatureVector i
    let L := ((curr - prev).norm + (next - curr).norm) / 2.0
    if L > 1e-10 then kVec.norm / L else 0.0

/-- Tangent vector at vertex i (pointing forward along curve) -/
def tangent (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n < 3 then Vec2.zero
  else
    let prev := c.vertex ((i + n - 1) % n)
    let next := c.vertex ((i + 1) % n)
    ((next - prev) * 0.5).normalize

/-- Normal vector at vertex i (perpendicular to tangent, pointing "outward") -/
def normal (c : Curve) (i : Nat) : Vec2 :=
  (c.tangent i).perp

/-! ## Curve Shortening Flow -/

/-- One step of curve shortening flow with explicit Euler integration.

    v_i(t+Δt) = v_i(t) + Δt * κN_i

    where κN_i is the discrete curvature vector at vertex i.

    The timestep should be small enough for stability:
    Δt < min(edge_length²) / 4 is a common stability criterion. -/
def step (c : Curve) (dt : Float) : Curve :=
  let n := c.numVertices
  let newVerts := (Array.range n).map fun i =>
    let v := c.vertex i
    let kVec := c.curvatureVector i
    v + dt * kVec
  ⟨newVerts⟩

/-- Adaptive timestep based on minimum edge length.
    Uses Δt = α * min(L²) where α < 0.25 for stability. -/
def adaptiveTimestep (c : Curve) (alpha : Float := 0.1) : Float :=
  let n := c.numVertices
  if n < 2 then 0.01
  else
    let minLenSq := (List.range n).foldl (init := Float.inf) fun acc i =>
      let L := (c.vertex (i + 1) - c.vertex i).normSq
      Float.min acc L
    alpha * minLenSq

/-- Run curve shortening for a given number of steps -/
def evolve (c : Curve) (steps : Nat) (dt : Float := 0.01) : Curve :=
  (List.range steps).foldl (init := c) fun curve _ => curve.step dt

/-- Run curve shortening with adaptive timestep until area reaches threshold -/
partial def evolveUntilArea (c : Curve) (targetArea : Float) (maxSteps : Nat := 10000) : Curve × Nat :=
  let rec go (curve : Curve) (stepNum : Nat) : Curve × Nat :=
    if stepNum >= maxSteps then (curve, stepNum)
    else if curve.area < targetArea then (curve, stepNum)
    else
      let dt := curve.adaptiveTimestep 0.1
      go (curve.step dt) (stepNum + 1)
  go c 0

/-! ## Curve Constructors -/

/-- Create a regular n-gon centered at origin with given radius -/
def regularPolygon (n : Nat) (radius : Float := 1.0) (center : Vec2 := Vec2.zero) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range n).map fun i =>
      let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
      ⟨center.x + radius * Float.cos θ, center.y + radius * Float.sin θ⟩
    ⟨verts⟩

/-- Create an ellipse approximation -/
def ellipse (a b : Float) (n : Nat := 64) (center : Vec2 := Vec2.zero) : Curve :=
  let verts := (Array.range n).map fun i =>
    let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
    ⟨center.x + a * Float.cos θ, center.y + b * Float.sin θ⟩
  ⟨verts⟩

/-- Create a star-shaped curve -/
def star (n : Nat) (outerRadius innerRadius : Float) (center : Vec2 := Vec2.zero) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range (2 * n)).map fun i =>
      let θ := Float.pi * i.toFloat / n.toFloat
      let r := if i % 2 = 0 then outerRadius else innerRadius
      ⟨center.x + r * Float.cos θ, center.y + r * Float.sin θ⟩
    ⟨verts⟩

/-- Create a figure-8 (lemniscate-like) curve -/
def figure8 (scale : Float := 1.0) (n : Nat := 64) : Curve :=
  let verts := (Array.range n).map fun i =>
    let t := 2.0 * Float.pi * i.toFloat / n.toFloat
    let x := scale * Float.sin t
    let y := scale * Float.sin t * Float.cos t
    ⟨x, y⟩
  ⟨verts⟩

end Curve

/-! ## Visualization Helpers -/

/-- Convert curve to SVG path string -/
def curveToSVGPath (c : Curve) (scale : Float := 100.0) (offset : Vec2 := ⟨200.0, 200.0⟩) : String :=
  if c.numVertices = 0 then ""
  else
    let start := c.vertex 0
    let startStr := s!"M {offset.x + scale * start.x} {offset.y - scale * start.y}"
    let pathStr := (List.range (c.numVertices - 1)).foldl (init := startStr) fun acc i =>
      let p := c.vertex (i + 1)
      acc ++ s!" L {offset.x + scale * p.x} {offset.y - scale * p.y}"
    pathStr ++ " Z"

/-- Generate SVG showing curve evolution -/
def evolutionSVG (initial : Curve) (steps : Nat) (dt : Float := 0.005) (everyNth : Nat := 50) : String :=
  let header := "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 400 400\">\n"
  let header := header ++ "  <rect width=\"400\" height=\"400\" fill=\"white\"/>\n"

  let rec go (c : Curve) (stepNum : Nat) (paths : String) (hue : Float) : String :=
    if stepNum >= steps then paths
    else
      let newC := c.step dt
      let newPaths := if stepNum % everyNth = 0 then
        let color := s!"hsl({hue}, 70%, 50%)"
        let opacity := 1.0 - (stepNum.toFloat / steps.toFloat) * 0.7
        paths ++ s!"  <path d=\"{curveToSVGPath newC}\" fill=\"none\" stroke=\"{color}\" stroke-width=\"1\" opacity=\"{opacity}\"/>\n"
      else paths
      go newC (stepNum + 1) newPaths (hue + 360.0 / (steps.toFloat / everyNth.toFloat))
  termination_by steps - stepNum

  let initialPath := s!"  <path d=\"{curveToSVGPath initial}\" fill=\"none\" stroke=\"blue\" stroke-width=\"2\"/>\n"
  let allPaths := go initial 0 initialPath 0.0
  let footer := "</svg>"
  header ++ allPaths ++ footer

/-! ## Demo / Tests -/

section Demo

/-- Demo: Curve shortening on a square -/
def demoSquare : IO Unit := do
  let square := Curve.regularPolygon 4 1.5
  IO.println s!"Initial square:"
  IO.println s!"  Vertices: {square.numVertices}"
  IO.println s!"  Arc length: {square.arcLength}"
  IO.println s!"  Area: {square.area}"

  let evolved := square.evolve 100 0.01
  IO.println s!"\nAfter 100 steps:"
  IO.println s!"  Arc length: {evolved.arcLength}"
  IO.println s!"  Area: {evolved.area}"

  -- Check vertices are becoming more circular
  let centroid := evolved.centroid
  let distances := evolved.vertices.map fun v => (v - centroid).norm
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"
  IO.println s!"  (Should approach 1.0 as curve becomes circular)"

/-- Demo: Curve shortening on a star -/
def demoStar : IO Unit := do
  let star := Curve.star 5 1.5 0.5
  IO.println s!"\nInitial 5-pointed star:"
  IO.println s!"  Vertices: {star.numVertices}"
  IO.println s!"  Arc length: {star.arcLength}"
  IO.println s!"  Area: {star.area}"

  -- Evolve with adaptive timestep
  let mut curve := star
  for _ in [:500] do
    let dt := curve.adaptiveTimestep 0.08
    curve := curve.step dt

  IO.println s!"\nAfter 500 adaptive steps:"
  IO.println s!"  Arc length: {curve.arcLength}"
  IO.println s!"  Area: {curve.area}"

  let centroid := curve.centroid
  let distances := curve.vertices.map fun v => (v - centroid).norm
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"

/-- Demo: Generate SVG visualization -/
def demoSVG : IO Unit := do
  let star := Curve.star 6 1.5 0.6
  let svg := evolutionSVG star 1000 0.002 100
  IO.println s!"\nGenerated SVG for curve evolution ({svg.length} chars)"
  IO.println "To view: save output to file.svg and open in browser"

/-- Run all demos -/
def runAllDemos : IO Unit := do
  IO.println "=== Curve Shortening Flow Demo ===\n"
  demoSquare
  demoStar
  demoSVG
  IO.println "\n=== Demo Complete ==="

end Demo

/-! ## Integration with Grassmann.MV (TODO)

To integrate with the MV-based geometric algebra:

1. Use MV sig .odd for 2D vectors (grade-1 multivectors)
2. The discrete curvature vector computation remains the same
3. The flow evolution can use GA operations:
   - Vector addition: MV.add
   - Scalar multiplication: MV.smul
   - Norm: sqrt(v ⋅ v) where ⋅ is the inner product

Example (pseudocode with MV):
```lean
def curvatureVectorGA (c : MVCurve) (i : Nat) : MV R2 .odd :=
  let prev := c.vertex (i - 1)
  let curr := c.vertex i
  let next := c.vertex (i + 1)
  next + (-2.0 * curr) + prev  -- Using MV arithmetic
```

The advantage of the GA formulation:
- Works in any dimension without code changes
- Curvature normal is automatically in the correct subspace
- Can extend to surface flow (mean curvature flow) naturally
-/

end Grassmann.CurveShortening
