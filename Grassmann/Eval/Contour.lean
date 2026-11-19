import Grassmann.Scene.Types

/-!
# Pure-Lean Marching-Triangles Contour Extractor & Intersection Solver

Replaces Swift's `EquationSystemCore` so implicit 2D curve extraction (`f(x,y) = 0`)
and multi-equation common-point detection (`f₁(x,y) = 0 ∧ f₂(x,y) = 0`) run 100% in Lean
and emit `Scene.ContourOverlay` directly into `GSIR` v1 frames.

Uses marching-triangles (each grid cell split diagonally into 2 CCW triangles —
eliminating marching-squares saddle ambiguity!), polyline stitching, and exact
spatial-hash segment-segment intersection solving.
-/

namespace Grassmann.Eval.Contour

open Grassmann.Scene

/-- A single 2D contour segment `(ax, ay) → (bx, by)`. -/
structure Seg2 where
  ax : Float
  ay : Float
  bx : Float
  by_ : Float
  deriving Repr, Inhabited

/-- Linear interpolation along an edge where `va` and `vb` straddle zero. -/
@[inline] private def interpEdge (ax ay va bx by_ vb : Float) : Vec2 :=
  let denom := va - vb
  let t := if Float.abs denom < 1e-15 then 0.5 else max 0.0 (min 1.0 (va / denom))
  ⟨ax + t * (bx - ax), ay + t * (by_ - ay)⟩

/-- Extract at most one zero-contour segment across a single triangle `(p0,v0), (p1,v1), (p2,v2)`. -/
private def marchTri (x0 y0 v0 x1 y1 v1 x2 y2 v2 : Float) : Option Seg2 :=
  let s0 := v0 >= 0.0
  let s1 := v1 >= 0.0
  let s2 := v2 >= 0.0
  if (s0 && s1 && s2) || (!s0 && !s1 && !s2) then none
  else
    -- Find the lone vertex whose sign differs from the other two
    if s0 != s1 && s0 != s2 then
      let pA := interpEdge x0 y0 v0 x1 y1 v1
      let pB := interpEdge x0 y0 v0 x2 y2 v2
      some ⟨pA.x, pA.y, pB.x, pB.y⟩
    else if s1 != s0 && s1 != s2 then
      let pA := interpEdge x1 y1 v1 x0 y0 v0
      let pB := interpEdge x1 y1 v1 x2 y2 v2
      some ⟨pA.x, pA.y, pB.x, pB.y⟩
    else
      let pA := interpEdge x2 y2 v2 x0 y0 v0
      let pB := interpEdge x2 y2 v2 x1 y1 v1
      some ⟨pA.x, pA.y, pB.x, pB.y⟩

/-- Sample `f(x, y)` on a `(gridN + 1) × (gridN + 1)` grid and extract zero-contour segments
using marching triangles. -/
def extractSegments (f : Float → Float → Float)
    (minX maxX minY maxY : Float) (gridN : Nat) : Array Seg2 := Id.run do
  let n := max 4 (min 160 gridN)
  let stride := n + 1
  let dx := (maxX - minX) / n.toFloat
  let dy := (maxY - minY) / n.toFloat
  let mut vals := FloatArray.emptyWithCapacity (stride * stride)
  for iy in [:stride] do
    let y := minY + iy.toFloat * dy
    for ix in [:stride] do
      let x := minX + ix.toFloat * dx
      let v := f x y
      vals := vals.push (if v.isFinite && !v.isNaN then v else 1e6)
  let mut segs : Array Seg2 := #[]
  for iy in [:n] do
    let y0 := minY + iy.toFloat * dy
    let y1 := y0 + dy
    let row0 := iy * stride
    let row1 := (iy + 1) * stride
    for ix in [:n] do
      let x0 := minX + ix.toFloat * dx
      let x1 := x0 + dx
      let v00 := vals.get! (row0 + ix)
      let v10 := vals.get! (row0 + ix + 1)
      let v01 := vals.get! (row1 + ix)
      let v11 := vals.get! (row1 + ix + 1)
      -- Split cell into 2 CCW triangles: (00,10,11) and (00,11,01)
      if let some s := marchTri x0 y0 v00 x1 y0 v10 x1 y1 v11 then
        segs := segs.push s
      if let some s := marchTri x0 y0 v00 x1 y1 v11 x0 y1 v01 then
        segs := segs.push s
  return segs

@[inline] private def distSq2 (x0 y0 x1 y1 : Float) : Float :=
  let dx := x0 - x1; let dy := y0 - y1
  dx * dx + dy * dy

/-- Stitch unordered 2D segments into connected `ContourPolyline` chains. -/
def stitchSegments (segs : Array Seg2) (color : RGBA) (width : Float := 2.2)
    (eps : Float := 1e-4) : Array ContourPolyline := Id.run do
  let m := segs.size
  if m == 0 then return #[]
  let eps2 := eps * eps
  let mut used := Array.replicate m false
  let mut curves : Array ContourPolyline := #[]
  for startIdx in [:m] do
    if !used[startIdx]! then
      used := used.set! startIdx true
      let s0 := segs[startIdx]!
      let mut chain : Array Vec2 := #[⟨s0.ax, s0.ay⟩, ⟨s0.bx, s0.by_⟩]
      -- Extend forward from tail
      let mut extended := true
      while extended do
        extended := false
        let tail := chain[chain.size - 1]!
        for j in [:m] do
          if !used[j]! then
            let sj := segs[j]!
            if distSq2 tail.x tail.y sj.ax sj.ay ≤ eps2 then
              used := used.set! j true
              chain := chain.push ⟨sj.bx, sj.by_⟩
              extended := true
              break
            else if distSq2 tail.x tail.y sj.bx sj.by_ ≤ eps2 then
              used := used.set! j true
              chain := chain.push ⟨sj.ax, sj.ay⟩
              extended := true
              break
      -- Extend backward from head
      let mut revPrefix : Array Vec2 := #[]
      let mut head := chain[0]!
      extended := true
      while extended do
        extended := false
        for j in [:m] do
          if !used[j]! then
            let sj := segs[j]!
            if distSq2 head.x head.y sj.bx sj.by_ ≤ eps2 then
              used := used.set! j true
              head := ⟨sj.ax, sj.ay⟩
              revPrefix := revPrefix.push head
              extended := true
              break
            else if distSq2 head.x head.y sj.ax sj.ay ≤ eps2 then
              used := used.set! j true
              head := ⟨sj.bx, sj.by_⟩
              revPrefix := revPrefix.push head
              extended := true
              break
      let totalPts := revPrefix.size + chain.size
      let mut pts := FloatArray.emptyWithCapacity (totalPts * 2)
      for k in [:revPrefix.size] do
        let p := revPrefix[revPrefix.size - 1 - k]!
        pts := pts.push p.x |>.push p.y
      for p in chain do
        pts := pts.push p.x |>.push p.y
      let firstX := pts.get! 0
      let firstY := pts.get! 1
      let lastX := pts.get! ((totalPts - 1) * 2)
      let lastY := pts.get! ((totalPts - 1) * 2 + 1)
      let isClosed := totalPts ≥ 4 && distSq2 firstX firstY lastX lastY ≤ eps2
      curves := curves.push { points := pts, color, width, closed := isClosed }
  return curves

/-- Exact 2D segment-segment intersection test (`0 ≤ t, u ≤ 1`). -/
private def intersectSeg2 (a b : Seg2) : Option Vec2 :=
  let r_x := a.bx - a.ax; let r_y := a.by_ - a.ay
  let s_x := b.bx - b.ax; let s_y := b.by_ - b.ay
  let denom := r_x * s_y - r_y * s_x
  if Float.abs denom < 1e-12 then none
  else
    let qp_x := b.ax - a.ax; let qp_y := b.ay - a.ay
    let t := (qp_x * s_y - qp_y * s_x) / denom
    let u := (qp_x * r_y - qp_y * r_x) / denom
    if t ≥ -1e-6 && t ≤ 1.0 + 1e-6 && u ≥ -1e-6 && u ≤ 1.0 + 1e-6 then
      let tc := max 0.0 (min 1.0 t)
      some ⟨a.ax + tc * r_x, a.ay + tc * r_y⟩
    else none

/-- Find all deduplicated pairwise intersections between distinct curve segment sets
using bounding-box rejection (exact replacement for Swift `EquationSystemCore`). -/
def findIntersections (segSets : Array (Array Seg2)) (dedupEps : Float := 0.03) :
    Array ContourIntersection := Id.run do
  let eps2 := dedupEps * dedupEps
  let mut pts : Array Vec2 := #[]
  for i in [:segSets.size] do
    let si := segSets[i]!
    for j in [(i + 1):segSets.size] do
      let sj := segSets[j]!
      for a in si do
        let aMinX := min a.ax a.bx - 1e-6
        let aMaxX := max a.ax a.bx + 1e-6
        let aMinY := min a.ay a.by_ - 1e-6
        let aMaxY := max a.ay a.by_ + 1e-6
        for b in sj do
          if max b.ax b.bx ≥ aMinX && min b.ax b.bx ≤ aMaxX &&
             max b.ay b.by_ ≥ aMinY && min b.ay b.by_ ≤ aMaxY then
            if let some p := intersectSeg2 a b then
              let dup := pts.any fun q => distSq2 p.x p.y q.x q.y ≤ eps2
              if !dup then pts := pts.push p
  let mut out : Array ContourIntersection := Array.mkEmpty pts.size
  for k in [:pts.size] do
    let p := pts[k]!
    out := out.push { x := p.x, y := p.y, color := RGBA.amber, label := s!"I{k + 1}" }
  return out

/-- Palette for multi-equation implicit contour plots. -/
def contourPalette (idx : Nat) : RGBA :=
  match idx % 6 with
  | 0 => RGBA.cyan
  | 1 => RGBA.coral
  | 2 => RGBA.green
  | 3 => RGBA.violet
  | 4 => RGBA.amber
  | _ => RGBA.blue

/-- Solve a system of implicit equations `fᵢ(x, y) = 0` completely in Lean, returning
a ready-to-render `Scene.ContourOverlay`. -/
def solveEquationSystem (fns : Array (Float → Float → Float))
    (minX maxX minY maxY : Float) (gridN : Nat := 48) : ContourOverlay := Id.run do
  let mut segSets : Array (Array Seg2) := Array.mkEmpty fns.size
  let mut allCurves : Array ContourPolyline := #[]
  for i in [:fns.size] do
    let segs := extractSegments fns[i]! minX maxX minY maxY gridN
    segSets := segSets.push segs
    let stitched := stitchSegments segs (contourPalette i) 2.4
    for cv in stitched do
      allCurves := allCurves.push cv
  let inters := findIntersections segSets
  return { minX, maxX, minY, maxY, curves := allCurves, intersections := inters }

end Grassmann.Eval.Contour
