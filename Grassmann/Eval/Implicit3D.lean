import Grassmann.Scene.Types

/-!
# Pure-Lean 3D Implicit Isosurface (Marching Tetrahedra) & Parametric Surface Engine

Strictly `Init`-only (`Grassmann.Scene.Types` only — zero `Lean.*`, zero `Std.*`,
zero external deps) so it links directly into both the tiny standalone C ABI dylib
and the Lean 4.36 → C → Emscripten WASM bundle.

Provides:
1. **O(1) Edge-Deduplicated Kuhn Marching Tetrahedra** (`marchingTetrahedra`) for
   arbitrary implicit surfaces `f(x, y, z) = iso`:
   - 6-tetrahedra Kuhn decomposition sharing the `(0,0,0) → (1,1,1)` cube diagonal
     (guaranteed watertight across all shared cell faces).
   - O(1) lattice edge cache (`7` directed Kuhn edges per grid vertex, zero hashing)
     delivering ~6× fewer vertices, ~6× fewer gradient calls, and compact `GSIR` meshes.
   - Analytical central-difference gradients `∇f(p)` as unit vertex normals, Laplacian
     curvature proxy for iridescent vertex colors, and per-triangle outward CCW
     winding enforcement (`dot((v1-v0)×(v2-v0), n0+n1+n2) ≥ 0`).
2. **Parametric 3D Surface Mesher** (`buildParametricSurface`) with exterior-product
   normals `normalize(∂S/∂u × ∂S/∂v)`, pole handling, curvature-driven iridescence,
   and optional double-sided backsheet for non-orientable manifolds.
3. **Canonical Showcase Surfaces**: Gyroid TPMS, Schwarz P, Animated Metaballs,
   Genus-2 Pretzel, Möbius Strip, Figure-8 Klein Bottle, Boy's Surface, Stereographic
   Clifford Torus (4D rotatable), Dupin Cyclide, Enneper Minimal Surface, Superquadrics.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval.Implicit3D

open Grassmann.Scene

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692

@[inline] private def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

@[inline] private def isFiniteF (x : Float) : Bool :=
  !x.isNaN && !x.isInf

/-- Smooth iridescent shader-ready vertex color driven by position, normal & curvature. -/
def iridescentColor (p n : Vec3) (curv : Float := 0.0) (alpha : Float := 1.0) : RGBA :=
  let h := clamp01 (0.5 + 0.35 * p.y)
  let c := clamp01 (0.5 + 0.25 * Float.tanh (curv * 0.35))
  let phase := 2.4 * h + 1.3 * c + 0.45 * (n.x * 0.5 + n.z * 0.5)
  let r := clamp01 (0.48 + 0.42 * Float.cos (phase + 0.0))
  let g := clamp01 (0.52 + 0.38 * Float.cos (phase + 2.0943951))
  let b := clamp01 (0.62 + 0.36 * Float.cos (phase + 4.1887902))
  ⟨r, g, b, clamp01 alpha⟩

/-- Compute FNV-1a dirty hash of a `MeshAsset` from vertex/index counts & sample floats. -/
private def meshHash (meshId : UInt64) (pos : FloatArray) (indices : Array UInt32) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  h := (h ^^^ meshId) * 1099511628211
  h := (h ^^^ pos.size.toUInt64) * 1099511628211
  h := (h ^^^ indices.size.toUInt64) * 1099511628211
  let step := max 1 (pos.size / 32)
  let mut i := 0
  while i < pos.size do
    h := (h ^^^ (pos.get! i).toBits) * 1099511628211
    i := i + step
  return h

/-! ## 1. Fast Watertight Kuhn Marching Tetrahedra (`f(x,y,z) = iso`) -/

/-- 2nd-order central-difference gradient & discrete Laplacian directly from the already-sampled
scalar `field` grid (`0` extra function evaluations!). Exact for all quadratic fields even on boundaries. -/
@[inline] private def gridGradAndLap (field : FloatArray) (nx1 ny1 nz1 : Nat)
    (inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 : Float)
    (ix iy iz : Nat) : Float × Float × Float × Float :=
  let slice := nx1 * ny1
  let base := iz * slice + iy * nx1 + ix
  let fc := field.get! base
  let (gx, d2x) :=
    if ix > 0 && ix + 1 < nx1 then
      let fp := field.get! (base + 1); let fm := field.get! (base - 1)
      ((fp - fm) * inv2Dx, (fp + fm - 2.0 * fc) * invDx2)
    else if ix == 0 && nx1 ≥ 3 then
      let f1 := field.get! (base + 1); let f2 := field.get! (base + 2)
      ((-3.0 * fc + 4.0 * f1 - f2) * inv2Dx, (fc - 2.0 * f1 + f2) * invDx2)
    else if ix + 1 == nx1 && nx1 ≥ 3 then
      let f1 := field.get! (base - 1); let f2 := field.get! (base - 2)
      ((3.0 * fc - 4.0 * f1 + f2) * inv2Dx, (fc - 2.0 * f1 + f2) * invDx2)
    else (0.0, 0.0)
  let (gy, d2y) :=
    if iy > 0 && iy + 1 < ny1 then
      let fp := field.get! (base + nx1); let fm := field.get! (base - nx1)
      ((fp - fm) * inv2Dy, (fp + fm - 2.0 * fc) * invDy2)
    else if iy == 0 && ny1 ≥ 3 then
      let f1 := field.get! (base + nx1); let f2 := field.get! (base + 2 * nx1)
      ((-3.0 * fc + 4.0 * f1 - f2) * inv2Dy, (fc - 2.0 * f1 + f2) * invDy2)
    else if iy + 1 == ny1 && ny1 ≥ 3 then
      let f1 := field.get! (base - nx1); let f2 := field.get! (base - 2 * nx1)
      ((3.0 * fc - 4.0 * f1 + f2) * inv2Dy, (fc - 2.0 * f1 + f2) * invDy2)
    else (0.0, 0.0)
  let (gz, d2z) :=
    if iz > 0 && iz + 1 < nz1 then
      let fp := field.get! (base + slice); let fm := field.get! (base - slice)
      ((fp - fm) * inv2Dz, (fp + fm - 2.0 * fc) * invDz2)
    else if iz == 0 && nz1 ≥ 3 then
      let f1 := field.get! (base + slice); let f2 := field.get! (base + 2 * slice)
      ((-3.0 * fc + 4.0 * f1 - f2) * inv2Dz, (fc - 2.0 * f1 + f2) * invDz2)
    else if iz + 1 == nz1 && nz1 ≥ 3 then
      let f1 := field.get! (base - slice); let f2 := field.get! (base - 2 * slice)
      ((3.0 * fc - 4.0 * f1 + f2) * inv2Dz, (fc - 2.0 * f1 + f2) * invDz2)
    else (0.0, 0.0)
  (gx, gy, gz, d2x + d2y + d2z)

private structure MtState where
  positions : FloatArray
  normals   : FloatArray
  colors    : FloatArray
  indices   : Array UInt32
  edgeCache : Array UInt32
  vertCount : UInt32

private def emitEdgeVertField (st : MtState) (field : FloatArray)
    (nx1 ny1 nz1 : Nat)
    (inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 : Float)
    (xs ys zs : FloatArray)
    (ixA iyA izA : Nat) (vA : Float)
    (ixB iyB izB : Nat) (vB : Float) : MtState × UInt32 :=
  let ⟨positions, normals, colors, indices, edgeCache, vertCount⟩ := st
  -- Canonical Kuhn edge ordering: smaller grid vertex first so dx, dy, dz ∈ {0, 1}
  let swap := !(ixA ≤ ixB && iyA ≤ iyB && izA ≤ izB)
  let ax := if swap then ixB else ixA
  let ay := if swap then iyB else iyA
  let az := if swap then izB else izA
  let bx := if swap then ixA else ixB
  let by_ := if swap then iyA else iyB
  let bz := if swap then izA else izB
  let dirCode := ((bx - ax) + 2 * (by_ - ay) + 4 * (bz - az)) - 1
  let slot := ((az * ny1 + ay) * nx1 + ax) * 7 + dirCode
  let cached := edgeCache.getD slot 0xFFFFFFFF
  if cached != 0xFFFFFFFF then
    (⟨positions, normals, colors, indices, edgeCache, vertCount⟩, cached)
  else
    let va := if swap then vB else vA
    let vb := if swap then vA else vB
    let denom := vb - va
    let tRaw := if Float.abs denom > 1e-12 then (-va) / denom else 0.5
    let t := clamp01 tRaw
    let pax := xs.get! ax; let pay := ys.get! ay; let paz := zs.get! az
    let px := pax + (xs.get! bx - pax) * t
    let py := pay + (ys.get! by_ - pay) * t
    let pz := paz + (zs.get! bz - paz) * t
    let (gax, gay, gaz, lapA) := gridGradAndLap field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 ax ay az
    let (gbx, gby, gbz, lapB) := gridGradAndLap field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 bx by_ bz
    let gx := gax + (gbx - gax) * t
    let gy := gay + (gby - gay) * t
    let gz := gaz + (gbz - gaz) * t
    let nLen := Float.sqrt (gx * gx + gy * gy + gz * gz)
    let n : Vec3 :=
      if nLen > 1e-9 && isFiniteF nLen then
        let invN := 1.0 / nLen
        ⟨gx * invN, gy * invN, gz * invN⟩
      else ⟨0.0, 1.0, 0.0⟩
    let lap := lapA + (lapB - lapA) * t
    let curv := if isFiniteF lap then lap / (max 0.25 nLen) else 0.0
    let col := iridescentColor ⟨px, py, pz⟩ n curv
    let vid := vertCount
    let positions := positions.push px |>.push py |>.push pz
    let normals   := normals.push n.x |>.push n.y |>.push n.z
    let colors    := colors.push col.r |>.push col.g |>.push col.b |>.push col.a
    let edgeCache := if h : slot < edgeCache.size then edgeCache.set slot vid h else edgeCache
    (⟨positions, normals, colors, indices, edgeCache, vid + 1⟩, vid)

private def pushOrientedTri (st : MtState) (i0 i1 i2 : UInt32) : MtState :=
  let ⟨positions, normals, colors, indices, edgeCache, vertCount⟩ := st
  let o0 := i0.toNat * 3
  let o1 := i1.toNat * 3
  let o2 := i2.toNat * 3
  let x0 := positions.get! o0; let y0 := positions.get! (o0 + 1); let z0 := positions.get! (o0 + 2)
  let dx1 := positions.get! o1 - x0; let dy1 := positions.get! (o1 + 1) - y0; let dz1 := positions.get! (o1 + 2) - z0
  let dx2 := positions.get! o2 - x0; let dy2 := positions.get! (o2 + 1) - y0; let dz2 := positions.get! (o2 + 2) - z0
  let fx := dy1 * dz2 - dz1 * dy2
  let fy := dz1 * dx2 - dx1 * dz2
  let fz := dx1 * dy2 - dy1 * dx2
  if fx * fx + fy * fy + fz * fz < 1e-18 then
    ⟨positions, normals, colors, indices, edgeCache, vertCount⟩
  else
    let anx := normals.get! o0 + normals.get! o1 + normals.get! o2
    let any := normals.get! (o0 + 1) + normals.get! (o1 + 1) + normals.get! (o2 + 1)
    let anz := normals.get! (o0 + 2) + normals.get! (o1 + 2) + normals.get! (o2 + 2)
    let indices :=
      if fx * anx + fy * any + fz * anz ≥ 0.0 then
        indices.push i0 |>.push i1 |>.push i2
      else
        indices.push i0 |>.push i2 |>.push i1
    ⟨positions, normals, colors, indices, edgeCache, vertCount⟩

@[inline] private def cornerVal (c : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : Float) : Float :=
  match c with
  | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3
  | 4 => v4 | 5 => v5 | 6 => v6 | _ => v7

@[inline] private def emitCellEdge (st : MtState) (field : FloatArray)
    (nx1 ny1 nz1 : Nat) (inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 : Float)
    (xs ys zs : FloatArray)
    (ix iy iz : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : Float) (a b : Nat) : MtState × UInt32 :=
  emitEdgeVertField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs
    (ix + (a &&& 1)) (iy + ((a >>> 1) &&& 1)) (iz + ((a >>> 2) &&& 1)) (cornerVal a v0 v1 v2 v3 v4 v5 v6 v7)
    (ix + (b &&& 1)) (iy + ((b >>> 1) &&& 1)) (iz + ((b >>> 2) &&& 1)) (cornerVal b v0 v1 v2 v3 v4 v5 v6 v7)

@[inline] private def emitTetField (st : MtState) (field : FloatArray)
    (nx1 ny1 nz1 : Nat) (inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 : Float)
    (xs ys zs : FloatArray)
    (ix iy iz : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : Float)
    (c0 c1 c2 c3 : Nat) (b0 b1 b2 b3 : Bool) : MtState :=
  let mask := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)
  match mask with
  | 1 | 14 =>
    let (s1, i0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c1
    let (s2, i1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c2
    let (s3, i2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c3
    pushOrientedTri s3 i0 i1 i2
  | 2 | 13 =>
    let (s1, i0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c0
    let (s2, i1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c2
    let (s3, i2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c3
    pushOrientedTri s3 i0 i1 i2
  | 4 | 11 =>
    let (s1, i0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c0
    let (s2, i1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c1
    let (s3, i2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c3
    pushOrientedTri s3 i0 i1 i2
  | 8 | 7 =>
    let (s1, i0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c3 c0
    let (s2, i1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c3 c1
    let (s3, i2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c3 c2
    pushOrientedTri s3 i0 i1 i2
  | 3 | 12 =>
    let (s1, q0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c2
    let (s2, q1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c3
    let (s3, q2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c3
    let (s4, q3) := emitCellEdge s3 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c2
    pushOrientedTri (pushOrientedTri s4 q0 q1 q2) q0 q2 q3
  | 5 | 10 =>
    let (s1, q0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c1
    let (s2, q1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c0 c3
    let (s3, q2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c3
    let (s4, q3) := emitCellEdge s3 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c1
    pushOrientedTri (pushOrientedTri s4 q0 q1 q2) q0 q2 q3
  | 6 | 9 =>
    let (s1, q0) := emitCellEdge st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c0
    let (s2, q1) := emitCellEdge s1 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c1 c3
    let (s3, q2) := emitCellEdge s2 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c3
    let (s4, q3) := emitCellEdge s3 field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 c2 c0
    pushOrientedTri (pushOrientedTri s4 q0 q1 q2) q0 q2 q3
  | _ => st

/-- Extract a watertight CCW `MeshAsset` directly from a pre-sampled `(nx+1)×(ny+1)×(nz+1)`
scalar `field` array using O(1) Kuhn edge deduplication and zero-eval 2nd-order interpolated
grid gradients! Zero closure calls during extraction. -/
def marchingTetrahedraField (field xs ys zs : FloatArray)
    (nx' ny' nz' : Nat) (dx dy dz : Float) (meshId : UInt64) : MeshAsset := Id.run do
  let nx1 := nx' + 1
  let ny1 := ny' + 1
  let nz1 := nz' + 1
  let totalPts := nx1 * ny1 * nz1
  let inv2Dx := 0.5 / max 1e-9 dx
  let inv2Dy := 0.5 / max 1e-9 dy
  let inv2Dz := 0.5 / max 1e-9 dz
  let invDx2 := 1.0 / max 1e-12 (dx * dx)
  let invDy2 := 1.0 / max 1e-12 (dy * dy)
  let invDz2 := 1.0 / max 1e-12 (dz * dz)
  let mut st : MtState :=
    { positions := FloatArray.emptyWithCapacity 4096
      normals   := FloatArray.emptyWithCapacity 4096
      colors    := FloatArray.emptyWithCapacity 4096
      indices   := Array.mkEmpty 8192
      edgeCache := Array.replicate (totalPts * 7) 0xFFFFFFFF
      vertCount := 0 }
  let sliceStride := nx1 * ny1
  for iz in [:nz'] do
    let zOff0 := iz * sliceStride
    let zOff1 := zOff0 + sliceStride
    for iy in [:ny'] do
      let yOff00 := zOff0 + iy * nx1
      let yOff01 := yOff00 + nx1
      let yOff10 := zOff1 + iy * nx1
      let yOff11 := yOff10 + nx1
      for ix in [:nx'] do
        let v0 := field.get! (yOff00 + ix)
        let v1 := field.get! (yOff00 + ix + 1)
        let v2 := field.get! (yOff01 + ix)
        let v3 := field.get! (yOff01 + ix + 1)
        let v4 := field.get! (yOff10 + ix)
        let v5 := field.get! (yOff10 + ix + 1)
        let v6 := field.get! (yOff11 + ix)
        let v7 := field.get! (yOff11 + ix + 1)
        let b0 := v0 < 0.0; let b1 := v1 < 0.0; let b2 := v2 < 0.0; let b3 := v3 < 0.0
        let b4 := v4 < 0.0; let b5 := v5 < 0.0; let b6 := v6 < 0.0; let b7 := v7 < 0.0
        let allIn  := b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7
        let allOut := !b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && !b7
        if !allIn && !allOut then
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 1 3 7 b0 b1 b3 b7
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 1 7 5 b0 b1 b7 b5
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 2 7 3 b0 b2 b7 b3
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 2 6 7 b0 b2 b6 b7
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 4 5 7 b0 b4 b5 b7
          st := emitTetField st field nx1 ny1 nz1 inv2Dx inv2Dy inv2Dz invDx2 invDy2 invDz2 xs ys zs ix iy iz v0 v1 v2 v3 v4 v5 v6 v7 0 4 7 6 b0 b4 b7 b6
  let h := meshHash meshId st.positions st.indices
  { meshId, dirtyHash := h, positions := st.positions, normals := st.normals,
    colors := st.colors, indices := st.indices }

/-- Zero-allocation unboxed-`Float` Kuhn Marching Tetrahedra (`f x y z = iso`) over `[bmin, bmax]`.
Evaluates `f` ONLY ONCE per grid vertex (`(nx+1)×(ny+1)×(nz+1)`) and derives exact 2nd-order
interpolated normals & curvature directly from the scalar grid! -/
@[specialize] def marchingTetrahedraXYZ (f : Float → Float → Float → Float)
    (bmin bmax : Vec3) (nx ny nz : Nat) (meshId : UInt64)
    (iso : Float := 0.0) (_gradEps : Float := 1.5e-3) : MeshAsset := Id.run do
  let nx' := max 4 (min 40 nx)
  let ny' := max 4 (min 40 ny)
  let nz' := max 4 (min 40 nz)
  let nx1 := nx' + 1
  let ny1 := ny' + 1
  let nz1 := nz' + 1
  let dx := (bmax.x - bmin.x) / Float.ofNat nx'
  let dy := (bmax.y - bmin.y) / Float.ofNat ny'
  let dz := (bmax.z - bmin.z) / Float.ofNat nz'
  let mut xs := FloatArray.emptyWithCapacity nx1
  for ix in [:nx1] do xs := xs.push (bmin.x + Float.ofNat ix * dx)
  let mut ys := FloatArray.emptyWithCapacity ny1
  for iy in [:ny1] do ys := ys.push (bmin.y + Float.ofNat iy * dy)
  let mut zs := FloatArray.emptyWithCapacity nz1
  for iz in [:nz1] do zs := zs.push (bmin.z + Float.ofNat iz * dz)
  let totalPts := nx1 * ny1 * nz1
  let mut field := FloatArray.emptyWithCapacity totalPts
  for iz in [:nz1] do
    let z := zs.get! iz
    for iy in [:ny1] do
      let y := ys.get! iy
      for ix in [:nx1] do
        field := field.push (f (xs.get! ix) y z - iso)
  return marchingTetrahedraField field xs ys zs nx' ny' nz' dx dy dz meshId

/-- Extract a watertight CCW `MeshAsset` of the zero-level isosurface `f(x, y, z) = iso`
over `[bmin, bmax]` at grid resolution `nx × ny × nz` using O(1) edge-cached Kuhn
Marching Tetrahedra. -/
def marchingTetrahedra (f : Vec3 → Float)
    (bmin bmax : Vec3) (nx ny nz : Nat) (meshId : UInt64)
    (iso : Float := 0.0) (gradEps : Float := 1.5e-3) : MeshAsset :=
  marchingTetrahedraXYZ (fun x y z => f ⟨x, y, z⟩) bmin bmax nx ny nz meshId iso gradEps

/-! ## 2. Parametric 3D Surface Mesher (`(u, v) → Vec3`) -/

/-- Sample a parametric 3D surface `surf : (u, v) → Vec3` on `[uMin, uMax] × [vMin, vMax]`
at resolution `nu × nv`, computing exact central-difference exterior normals
`normalize(∂S/∂u × ∂S/∂v)` and curvature-driven iridescent vertex colors.
Set `doubleSided := true` for non-orientable surfaces (Möbius strip, Klein bottle, Boy's surface)
or open sheets (Enneper). -/
def buildParametricSurface (surf : Float → Float → Vec3)
    (uMin uMax vMin vMax : Float) (nu nv : Nat)
    (meshId : UInt64) (doubleSided : Bool := false) (alpha : Float := 1.0) : MeshAsset := Id.run do
  let nu' := max 6 (min 96 nu)
  let nv' := max 6 (min 96 nv)
  let du := (uMax - uMin) / Float.ofNat nu'
  let dv := (vMax - vMin) / Float.ofNat nv'
  let epsU := max 1e-4 (du * 0.05)
  let epsV := max 1e-4 (dv * 0.05)
  let stride := nv' + 1
  let baseVerts := (nu' + 1) * stride
  let totalVerts := if doubleSided then baseVerts * 2 else baseVerts
  let mut positions := FloatArray.emptyWithCapacity (totalVerts * 3)
  let mut normals   := FloatArray.emptyWithCapacity (totalVerts * 3)
  let mut colors    := FloatArray.emptyWithCapacity (totalVerts * 4)
  let mut indices   := Array.mkEmpty ((if doubleSided then 12 else 6) * nu' * nv')
  -- Front sheet
  for iu in [:nu' + 1] do
    let u := uMin + Float.ofNat iu * du
    for iv in [:nv' + 1] do
      let v := vMin + Float.ofNat iv * dv
      let p := surf u v
      let pUp := surf (u + epsU) v
      let pUm := surf (u - epsU) v
      let pVp := surf u (v + epsV)
      let pVm := surf u (v - epsV)
      let su := Vec3.scale (1.0 / (2.0 * epsU)) (Vec3.sub pUp pUm)
      let sv := Vec3.scale (1.0 / (2.0 * epsV)) (Vec3.sub pVp pVm)
      let rawN := Vec3.cross su sv
      let nLen := Vec3.norm rawN
      let n :=
        if nLen > 1e-8 && isFiniteF nLen then Vec3.scale (1.0 / nLen) rawN
        else
          -- Graceful pole fallback using radial direction
          let pLen := Vec3.norm p
          if pLen > 1e-6 then Vec3.scale (1.0 / pLen) p else ⟨0.0, 1.0, 0.0⟩
      let suu := Vec3.scale (1.0 / (epsU * epsU)) (Vec3.sub (Vec3.add pUp pUm) (Vec3.scale 2.0 p))
      let svv := Vec3.scale (1.0 / (epsV * epsV)) (Vec3.sub (Vec3.add pVp pVm) (Vec3.scale 2.0 p))
      let curv := Vec3.dot (Vec3.add suu svv) n * 0.15
      let col := iridescentColor p n curv alpha
      positions := positions.push p.x |>.push p.y |>.push p.z
      normals   := normals.push n.x |>.push n.y |>.push n.z
      colors    := colors.push col.r |>.push col.g |>.push col.b |>.push col.a
  for iu in [:nu'] do
    for iv in [:nv'] do
      let i00 := UInt32.ofNat (iu * stride + iv)
      let i10 := UInt32.ofNat ((iu + 1) * stride + iv)
      let i11 := UInt32.ofNat ((iu + 1) * stride + iv + 1)
      let i01 := UInt32.ofNat (iu * stride + iv + 1)
      indices := indices.push i00 |>.push i10 |>.push i11
                        |>.push i00 |>.push i11 |>.push i01
  if doubleSided then
    -- Duplicate vertices with negated normals & reversed CCW winding for non-orientable surfaces
    let offset := UInt32.ofNat baseVerts
    for k in [:baseVerts] do
      let o3 := k * 3
      let o4 := k * 4
      positions := positions.push (positions.get! o3) |>.push (positions.get! (o3 + 1)) |>.push (positions.get! (o3 + 2))
      normals   := normals.push (-(normals.get! o3)) |>.push (-(normals.get! (o3 + 1))) |>.push (-(normals.get! (o3 + 2)))
      colors    := colors.push (colors.get! o4) |>.push (colors.get! (o4 + 1)) |>.push (colors.get! (o4 + 2)) |>.push (colors.get! (o4 + 3))
    for iu in [:nu'] do
      for iv in [:nv'] do
        let i00 := offset + UInt32.ofNat (iu * stride + iv)
        let i10 := offset + UInt32.ofNat ((iu + 1) * stride + iv)
        let i11 := offset + UInt32.ofNat ((iu + 1) * stride + iv + 1)
        let i01 := offset + UInt32.ofNat (iu * stride + iv + 1)
        indices := indices.push i00 |>.push i11 |>.push i10
                          |>.push i00 |>.push i01 |>.push i11
  let h := meshHash meshId positions indices
  { meshId, dirtyHash := h, positions, normals, colors, indices }

/-! ## 3. Canonical Implicit Isosurface Builders -/

/-- **Gyroid TPMS** minimal surface: `sin(kx)cos(ky) + sin(ky)cos(kz) + sin(kz)cos(kx) = iso`.
Fast at `18³` (6,859 grid samples). -/
def buildGyroidMesh (iso : Float := 0.0) (freq : Float := 2.4) (gridN : Nat := 18)
    (meshId : UInt64 := 3001) : MeshAsset :=
  let f (px py pz : Float) : Float :=
    let x := px * freq; let y := py * freq; let z := pz * freq
    let g := Float.sin x * Float.cos y + Float.sin y * Float.cos z + Float.sin z * Float.cos x - iso
    -- Soft spherical bounding shell so Gyroid floats cleanly as a closed organic sculpture
    let r2 := px * px + py * py + pz * pz
    let mask := r2 - 1.75
    if mask > g then mask else g
  marchingTetrahedraXYZ f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Schwarz P** triply periodic minimal surface: `cos(kx) + cos(ky) + cos(kz) = iso`. -/
def buildSchwarzPMesh (iso : Float := 0.0) (freq : Float := 2.35) (gridN : Nat := 18)
    (meshId : UInt64 := 3002) : MeshAsset :=
  let f (px py pz : Float) : Float :=
    let x := px * freq; let y := py * freq; let z := pz * freq
    let s := Float.cos x + Float.cos y + Float.cos z - iso
    let r2 := px * px + py * py + pz * pz
    let mask := r2 - 1.85
    if mask > s then mask else s
  marchingTetrahedraXYZ f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Animated 4-Lobe Organic Metaballs**: `1.0 - ∑ rᵢ² / (‖p - cᵢ(t)‖² + 0.04) = 0`.
`ctrl` moves lobe 0 interactively! -/
def buildMetaballsMesh (t : Float) (ctrl : Vec3 := ⟨0.55, 0.25, 0.0⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 3003) : MeshAsset :=
  let c0x := ctrl.x; let c0y := ctrl.y; let c0z := ctrl.z
  let c1x := -0.58 * Float.cos (t * 0.9); let c1y := 0.42 * Float.sin (t * 1.1); let c1z := 0.35 * Float.sin (t * 0.7)
  let c2x := 0.32 * Float.sin (t * 1.3); let c2y := -0.52 * Float.cos (t * 0.8); let c2z := -0.40 * Float.cos (t * 1.0)
  let c3x := -0.25 * Float.sin (t * 0.6); let c3y := -0.20 * Float.sin (t * 1.2); let c3z := 0.55 * Float.cos (t * 0.85)
  let f (px py pz : Float) : Float :=
    let dx0 := px - c0x; let dy0 := py - c0y; let dz0 := pz - c0z
    let dx1 := px - c1x; let dy1 := py - c1y; let dz1 := pz - c1z
    let dx2 := px - c2x; let dy2 := py - c2y; let dz2 := pz - c2z
    let dx3 := px - c3x; let dy3 := py - c3y; let dz3 := pz - c3z
    let d0 := dx0 * dx0 + dy0 * dy0 + dz0 * dz0 + 0.04
    let d1 := dx1 * dx1 + dy1 * dy1 + dz1 * dz1 + 0.04
    let d2 := dx2 * dx2 + dy2 * dy2 + dz2 * dz2 + 0.04
    let d3 := dx3 * dx3 + dy3 * dy3 + dz3 * dz3 + 0.04
    1.0 - (0.20 / d0 + 0.18 / d1 + 0.16 / d2 + 0.15 / d3)
  marchingTetrahedraXYZ f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Genus-2 Double-Torus Pretzel**: `((x² + y²)² - x² + y²)² + z² - r² = 0`. -/
def buildGenus2Mesh (tubeR : Float := 0.22) (gridN : Nat := 20)
    (meshId : UInt64 := 3004) : MeshAsset :=
  let r2 := tubeR * tubeR
  let f (px py pz : Float) : Float :=
    let x2 := px * px; let y2 := py * py; let z2 := pz * pz
    let q := (x2 + y2) * (x2 + y2) - x2 + y2
    q * q + z2 - r2
  marchingTetrahedraXYZ f ⟨-1.35, -1.0, -0.55⟩ ⟨1.35, 1.0, 0.55⟩ gridN gridN (max 10 (gridN / 2)) meshId

/-! ## 4. Canonical Parametric 3D Surface Builders -/

/-- **Möbius Strip** (`doubleSided := true`) with interactive half-twist count `twists` (default 1). -/
def buildMobiusStripMesh (R : Float := 1.0) (halfWidth : Float := 0.38) (twists : Float := 1.0)
    (nu : Nat := 64) (nv : Nat := 14) (meshId : UInt64 := 3101) : MeshAsset :=
  let surf (u v : Float) : Vec3 :=
    let half := 0.5 * twists * u
    let r := R + v * Float.cos half
    ⟨r * Float.cos u, v * Float.sin half, r * Float.sin u⟩
  buildParametricSurface surf 0.0 twoPiF (-halfWidth) halfWidth nu nv meshId true

/-- **Figure-8 Klein Bottle** immersion (`doubleSided := true`) with adjustable tube radius `rTube`. -/
def buildKleinBottleMesh (R : Float := 1.05) (rTube : Float := 0.42)
    (nu : Nat := 56) (nv : Nat := 28) (meshId : UInt64 := 3102) : MeshAsset :=
  let surf (u v : Float) : Vec3 :=
    let cu := Float.cos u; let su := Float.sin u
    let cu2 := Float.cos (0.5 * u); let su2 := Float.sin (0.5 * u)
    let sv := Float.sin v; let s2v := Float.sin (2.0 * v)
    let rad := R + rTube * (cu2 * sv - su2 * s2v)
    ⟨rad * cu, rTube * (su2 * sv + cu2 * s2v), rad * su⟩
  buildParametricSurface surf 0.0 twoPiF 0.0 twoPiF nu nv meshId true

/-- **Boy's Surface** (Apéry-Bryant immersion of real projective plane `ℝP²`, `doubleSided := true`). -/
def buildBoysSurfaceMesh (scale : Float := 0.85) (nu : Nat := 44) (nv : Nat := 28)
    (meshId : UInt64 := 3103) : MeshAsset :=
  let sq2 := Float.sqrt 2.0
  let surf (u v : Float) : Vec3 :=
    -- u ∈ [-π/2, π/2], v ∈ [0, π]
    let cu := Float.cos u
    let c2v := Float.cos (2.0 * v); let s2v := Float.sin (2.0 * v)
    let cv := Float.cos v; let sv := Float.sin v
    let denom := max 0.15 (2.0 - sq2 * Float.sin (3.0 * v) * Float.sin (2.0 * u))
    let x := (sq2 * cu * cu * c2v + cu * sv) / denom
    let y := (sq2 * cu * cu * s2v - cu * cv) / denom
    let z := (3.0 * cu * cu) / denom - 1.0
    ⟨x * scale, z * scale, y * scale⟩
  buildParametricSurface surf (-0.5 * piF) (0.5 * piF) 0.0 piF nu nv meshId true

/-- **Stereographic Clifford Torus** (`S¹ × S¹ ⊂ S³ → ℝ³`) rotated in 4D by `angle4D`
(sweeps smoothly through a symmetric torus & nested Villarceau rings!). -/
def buildCliffordTorusMesh (angle4D : Float := 0.0) (scale : Float := 0.72)
    (nu : Nat := 48) (nv : Nat := 28) (meshId : UInt64 := 3104) : MeshAsset :=
  let invSq2 := 0.7071067811865476
  let ca := Float.cos angle4D; let sa := Float.sin angle4D
  let surf (u v : Float) : Vec3 :=
    let x0 := invSq2 * Float.cos u
    let y0 := invSq2 * Float.sin u
    let z0 := invSq2 * Float.cos v
    let w0 := invSq2 * Float.sin v
    -- 4D rotation in the (x, w) plane keeps the torus on S³ while turning it inside-out in ℝ³!
    let x4 := ca * x0 - sa * w0
    let w4 := sa * x0 + ca * w0
    let denom := max 0.28 (1.0 - w4)
    ⟨scale * x4 / denom, scale * z0 / denom, scale * y0 / denom⟩
  buildParametricSurface surf 0.0 twoPiF 0.0 twoPiF nu nv meshId false

/-- **Dupin Cyclide** (conformal image of a torus in `CGA3` — envelope of spheres tangent to 3 spheres).
Parameters satisfy `c² = a² - b²` with `a > c ≥ 0` and ring radius `d > c`. -/
def buildDupinCyclideMesh (a : Float := 1.0) (c : Float := 0.35) (d : Float := 0.62)
    (nu : Nat := 48) (nv : Nat := 28) (meshId : UInt64 := 3105) : MeshAsset :=
  let c' := min (a * 0.85) (max 0.0 c)
  let b := Float.sqrt (max 0.04 (a * a - c' * c'))
  let surf (u v : Float) : Vec3 :=
    let cu := Float.cos u; let su := Float.sin u
    let cv := Float.cos v; let sv := Float.sin v
    let denom := max 0.2 (a - c' * cu * cv)
    let x := (d * (c' - a * cu * cv) + b * b * cu) / denom
    let y := (b * su * (a - d * cv)) / denom
    let z := (b * sv * (c' * cu - d)) / denom
    ⟨x, z, y⟩
  buildParametricSurface surf 0.0 twoPiF 0.0 twoPiF nu nv meshId false

/-- **Enneper Minimal Surface** (`doubleSided := true`, zero mean curvature everywhere). -/
def buildEnneperSurfaceMesh (bound : Float := 1.15) (scale : Float := 0.42)
    (nu : Nat := 32) (nv : Nat := 32) (meshId : UInt64 := 3106) : MeshAsset :=
  let surf (u v : Float) : Vec3 :=
    let x := u - (u * u * u) / 3.0 + u * v * v
    let y := v - (v * v * v) / 3.0 + v * u * u
    let z := u * u - v * v
    ⟨x * scale, z * scale, y * scale⟩
  buildParametricSurface surf (-bound) bound (-bound) bound nu nv meshId true

/-- Signed power `sign(x) * |x|^p` used by superquadric parameterizations. -/
private def spow (x p : Float) : Float :=
  let ax := Float.abs x
  if ax < 1e-9 then 0.0
  else
    let v := Float.pow ax p
    if x < 0.0 then -v else v

/-- **Superquadric Surface** morphing smoothly between star (`e < 0.5`), octahedron (`e = 2`),
sphere (`e = 1`), and rounded cube (`e = 0.25`). -/
def buildSuperquadricMesh (e1 : Float := 0.45) (e2 : Float := 0.45) (scale : Float := 1.0)
    (nu : Nat := 36) (nv : Nat := 24) (meshId : UInt64 := 3107) : MeshAsset :=
  let surf (u v : Float) : Vec3 :=
    -- u ∈ [-π, π], v ∈ [-π/2, π/2]
    let cv := Float.cos v; let sv := Float.sin v
    let cu := Float.cos u; let su := Float.sin u
    let rc := spow cv e1
    ⟨scale * rc * spow cu e2, scale * spow sv e1, scale * rc * spow su e2⟩
  buildParametricSurface surf (-piF) piF (-0.495 * piF) (0.495 * piF) nu nv meshId false

end Grassmann.Eval.Implicit3D
