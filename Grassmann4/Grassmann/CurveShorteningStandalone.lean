/-
  CurveShorteningStandalone.lean - Curve Shortening Flow Demo

  A standalone implementation that avoids SciLean dependency.
  Uses simple 2D vectors as (Float × Float) pairs.

  Curve shortening flow: ∂γ/∂t = κN
  where κ is curvature and N is the unit normal.
  Using discrete Laplacian: κN ≈ (v_{i+1} - 2vᵢ + v_{i-1})
-/

namespace CurveShortening

/-! ## 2D Vector Operations -/

abbrev Vec2 := Float × Float

@[inline] def vec2 (x y : Float) : Vec2 := (x, y)
@[inline] def getX (v : Vec2) : Float := v.1
@[inline] def getY (v : Vec2) : Float := v.2

@[inline] def vadd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)
@[inline] def vsub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)
@[inline] def vsmul (s : Float) (v : Vec2) : Vec2 := (s * v.1, s * v.2)
@[inline] def vneg (v : Vec2) : Vec2 := (-v.1, -v.2)

@[inline] def dot (a b : Vec2) : Float := a.1 * b.1 + a.2 * b.2
@[inline] def normSq (v : Vec2) : Float := dot v v
@[inline] def norm (v : Vec2) : Float := Float.sqrt (normSq v)

@[inline] def normalize (v : Vec2) : Vec2 :=
  let n := norm v
  if n > 1e-10 then vsmul (1.0 / n) v else (0.0, 0.0)

/-- Cross product in 2D (returns z-component) -/
@[inline] def cross (a b : Vec2) : Float := a.1 * b.2 - a.2 * b.1

/-- Rotate 90° counter-clockwise: (x, y) → (-y, x)
    This is conceptually v * I where I is the pseudoscalar e₁₂ -/
@[inline] def rotateCCW (v : Vec2) : Vec2 := (-v.2, v.1)

/-- Rotate 90° clockwise: (x, y) → (y, -x) -/
@[inline] def rotateCW (v : Vec2) : Vec2 := (v.2, -v.1)

def Float.pi : Float := 3.14159265358979323846
def Float.inf : Float := 1.0 / 0.0
@[inline] def Float.min (a b : Float) : Float := if a ≤ b then a else b
@[inline] def Float.max (a b : Float) : Float := if a ≥ b then a else b

/-! ## Discrete Curve -/

structure Curve where
  vertices : Array Vec2
  deriving Inhabited

namespace Curve

@[inline] def numVertices (c : Curve) : Nat := c.vertices.size

/-- Get vertex with wrapping for closed curves -/
@[inline] def vertex (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n = 0 then (0.0, 0.0)
  else c.vertices[i % n]!

/-- Total arc length -/
def arcLength (c : Curve) : Float :=
  let n := c.numVertices
  (List.range n).foldl (init := 0.0) fun acc i =>
    acc + norm (vsub (c.vertex (i + 1)) (c.vertex i))

/-- Centroid -/
def centroid (c : Curve) : Vec2 :=
  let n := c.numVertices
  if n = 0 then (0.0, 0.0)
  else
    let sum := c.vertices.foldl (init := (0.0, 0.0)) vadd
    vsmul (1.0 / n.toFloat) sum

/-- Signed area via shoelace formula -/
def signedArea (c : Curve) : Float :=
  let n := c.numVertices
  let sum := (List.range n).foldl (init := 0.0) fun acc i =>
    acc + cross (c.vertex i) (c.vertex (i + 1))
  sum / 2.0

def area (c : Curve) : Float := Float.abs c.signedArea

/-! ## Curvature -/

/-- Discrete curvature vector: κN ≈ (v_{i+1} - 2vᵢ + v_{i-1}) -/
@[inline]
def curvatureVector (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n < 3 then (0.0, 0.0)
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    vadd (vsub next (vsmul 2.0 curr)) prev

/-- Tangent at vertex i -/
def tangent (c : Curve) (i : Nat) : Vec2 :=
  let n := c.numVertices
  if n < 3 then (0.0, 0.0)
  else
    let prev := c.vertex ((i + n - 1) % n)
    let next := c.vertex ((i + 1) % n)
    normalize (vsmul 0.5 (vsub next prev))

/-- Normal at vertex i: N = T rotated 90° CCW -/
def normal (c : Curve) (i : Nat) : Vec2 :=
  rotateCCW (c.tangent i)

/-- Curvature magnitude -/
def curvature (c : Curve) (i : Nat) : Float :=
  let n := c.numVertices
  if n < 3 then 0.0
  else
    let prev := c.vertex ((i + n - 1) % n)
    let curr := c.vertex i
    let next := c.vertex ((i + 1) % n)
    let kVec := c.curvatureVector i
    let L := (norm (vsub curr prev) + norm (vsub next curr)) / 2.0
    if L > 1e-10 then norm kVec / L else 0.0

/-! ## Curve Shortening Flow -/

/-- One step: v_i(t+Δt) = v_i(t) + Δt * κN_i -/
def step (c : Curve) (dt : Float) : Curve :=
  let n := c.numVertices
  let newVerts := (Array.range n).map fun i =>
    let v := c.vertex i
    let kVec := c.curvatureVector i
    vadd v (vsmul dt kVec)
  ⟨newVerts⟩

/-- Adaptive timestep based on min edge length -/
def adaptiveTimestep (c : Curve) (alpha : Float := 0.1) : Float :=
  let n := c.numVertices
  if n < 2 then 0.01
  else
    let minLenSq := (List.range n).foldl (init := Float.inf) fun acc i =>
      Float.min acc (normSq (vsub (c.vertex (i + 1)) (c.vertex i)))
    alpha * minLenSq

/-- Run curve shortening for given steps -/
def evolve (c : Curve) (steps : Nat) (dt : Float := 0.01) : Curve :=
  (List.range steps).foldl (init := c) fun curve _ => curve.step dt

/-! ## Constructors -/

/-- Regular n-gon -/
def regularPolygon (n : Nat) (radius : Float := 1.0) (center : Vec2 := (0.0, 0.0)) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range n).map fun i =>
      let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
      vadd center (vec2 (radius * Float.cos θ) (radius * Float.sin θ))
    ⟨verts⟩

/-- Ellipse -/
def ellipse (a b : Float) (n : Nat := 64) (center : Vec2 := (0.0, 0.0)) : Curve :=
  let verts := (Array.range n).map fun i =>
    let θ := 2.0 * Float.pi * i.toFloat / n.toFloat
    vadd center (vec2 (a * Float.cos θ) (b * Float.sin θ))
  ⟨verts⟩

/-- Star -/
def star (n : Nat) (outerR innerR : Float) (center : Vec2 := (0.0, 0.0)) : Curve :=
  if n < 3 then ⟨#[]⟩
  else
    let verts := (Array.range (2 * n)).map fun i =>
      let θ := Float.pi * i.toFloat / n.toFloat
      let r := if i % 2 = 0 then outerR else innerR
      vadd center (vec2 (r * Float.cos θ) (r * Float.sin θ))
    ⟨verts⟩

end Curve

/-! ## SVG Visualization -/

def curveToSVGPath (c : Curve) (scale : Float := 100.0) (ox oy : Float := 200.0) : String :=
  if c.numVertices = 0 then ""
  else
    let start := c.vertex 0
    let startStr := s!"M {ox + scale * start.1} {oy - scale * start.2}"
    let pathStr := (List.range (c.numVertices - 1)).foldl (init := startStr) fun acc i =>
      let p := c.vertex (i + 1)
      acc ++ s!" L {ox + scale * p.1} {oy - scale * p.2}"
    pathStr ++ " Z"

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
        paths ++ s!"  <path d=\"{curveToSVGPath newC}\" fill=\"none\" stroke=\"{color}\" stroke-width=\"1\" opacity=\"{opacity}\"/>\n"
      else paths
      go newC (stepNum + 1) newPaths (hue + 360.0 / (steps.toFloat / everyNth.toFloat))
  termination_by steps - stepNum
  let initialPath := s!"  <path d=\"{curveToSVGPath initial}\" fill=\"none\" stroke=\"blue\" stroke-width=\"2\"/>\n"
  let allPaths := go initial 0 initialPath 0.0
  header ++ allPaths ++ "</svg>"

/-! ## Demo -/

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
  let cent := evolved.centroid
  let distances := evolved.vertices.map fun v => norm (vsub v cent)
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"
  IO.println s!"  (Approaches 1.0 as curve becomes circular)"

def demoTangentNormal : IO Unit := do
  IO.println s!"\n--- Tangent and Normal ---"
  let circle := Curve.regularPolygon 8 1.0
  for i in [:4] do
    let T := circle.tangent i
    let N := circle.normal i
    IO.println s!"Vertex {i}: T = ({T.1}, {T.2}), N = ({N.1}, {N.2})"
    IO.println s!"  T·N = {dot T N} (should be ≈0)"

def demoStar : IO Unit := do
  let star := Curve.star 5 1.5 0.5
  IO.println s!"\nInitial 5-pointed star:"
  IO.println s!"  Vertices: {star.numVertices}"
  IO.println s!"  Arc length: {star.arcLength}"
  IO.println s!"  Area: {star.area}"
  let mut curve := star
  for _ in [:200] do
    let dt := curve.adaptiveTimestep 0.08
    curve := curve.step dt
  IO.println s!"\nAfter 200 adaptive steps:"
  IO.println s!"  Arc length: {curve.arcLength}"
  IO.println s!"  Area: {curve.area}"
  let cent := curve.centroid
  let distances := curve.vertices.map fun v => norm (vsub v cent)
  let minDist := distances.foldl Float.min Float.inf
  let maxDist := distances.foldl Float.max 0.0
  IO.println s!"  Distance ratio (max/min): {maxDist / minDist}"

def runAllDemos : IO Unit := do
  IO.println "=== Curve Shortening Flow Demo ===\n"
  demoSquare
  demoTangentNormal
  demoStar
  IO.println "\n=== Demo Complete ==="

end CurveShortening
