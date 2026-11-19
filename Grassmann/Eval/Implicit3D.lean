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

/-- Six positively-oriented Kuhn tetrahedra partitioning the unit cube `[0,1]³`.
Corner bitmask `b = dx + 2*dy + 4*dz` (`0=(0,0,0)` .. `7=(1,1,1)`).
Every tetrahedron edge `(u, v)` ordered with `u < v` satisfies `dx, dy, dz ∈ {0, 1}`,
so edges map bijectively into the 7-direction lattice edge table! -/
private def kuhnTets : Array (Nat × Nat × Nat × Nat) :=
  #[ (0, 1, 3, 7)
   , (0, 1, 7, 5)
   , (0, 2, 7, 3)
   , (0, 2, 6, 7)
   , (0, 4, 5, 7)
   , (0, 4, 7, 6) ]

/-- Central-difference gradient normal & discrete Laplacian curvature proxy at `p`. -/
private def gradAndCurv (f : Vec3 → Float) (p : Vec3) (eps : Float) : Vec3 × Float :=
  let fxP := f ⟨p.x + eps, p.y, p.z⟩
  let fxM := f ⟨p.x - eps, p.y, p.z⟩
  let fyP := f ⟨p.x, p.y + eps, p.z⟩
  let fyM := f ⟨p.x, p.y - eps, p.z⟩
  let fzP := f ⟨p.x, p.y, p.z + eps⟩
  let fzM := f ⟨p.x, p.y, p.z - eps⟩
  let fc  := f p
  let gx := (fxP - fxM) / (2.0 * eps)
  let gy := (fyP - fyM) / (2.0 * eps)
  let gz := (fzP - fzM) / (2.0 * eps)
  let g : Vec3 := ⟨gx, gy, gz⟩
  let nLen := Vec3.norm g
  let n := if nLen > 1e-9 && isFiniteF nLen then Vec3.scale (1.0 / nLen) g else ⟨0.0, 1.0, 0.0⟩
  let lap := (fxP + fxM + fyP + fyM + fzP + fzM - 6.0 * fc) / (eps * eps)
  let curv := if isFiniteF lap then lap / (max 0.25 nLen) else 0.0
  (n, curv)

private structure MtState where
  positions : FloatArray
  normals   : FloatArray
  colors    : FloatArray
  indices   : Array UInt32
  edgeCache : Array UInt32
  vertCount : UInt32

private def emitEdgeVert (st : MtState) (f : Vec3 → Float) (eps : Float)
    (nx1 ny1 : Nat)
    (ixA iyA izA : Nat) (pA : Vec3) (vA : Float)
    (ixB iyB izB : Nat) (pB : Vec3) (vB : Float) : MtState × UInt32 :=
  -- Canonical Kuhn edge ordering: smaller grid vertex first so dx, dy, dz ∈ {0, 1}
  let (ax, ay, az, pa, va, bx, by_, bz, pb, vb) :=
    if ixA ≤ ixB && iyA ≤ iyB && izA ≤ izB then
      (ixA, iyA, izA, pA, vA, ixB, iyB, izB, pB, vB)
    else
      (ixB, iyB, izB, pB, vB, ixA, iyA, izA, pA, vA)
  let dx := bx - ax
  let dy := by_ - ay
  let dz := bz - az
  let dirCode := (dx + 2 * dy + 4 * dz) - 1
  let slot := ((az * ny1 + ay) * nx1 + ax) * 7 + dirCode
  let cached := st.edgeCache.getD slot 0xFFFFFFFF
  if cached != 0xFFFFFFFF then
    (st, cached)
  else
    let denom := vb - va
    let tRaw := if Float.abs denom > 1e-12 then (-va) / denom else 0.5
    let t := clamp01 tRaw
    let p := Vec3.lerp pa pb t
    let (n, curv) := gradAndCurv f p eps
    let col := iridescentColor p n curv
    let vid := st.vertCount
    let st' : MtState :=
      { positions := st.positions.push p.x |>.push p.y |>.push p.z
        normals   := st.normals.push n.x |>.push n.y |>.push n.z
        colors    := st.colors.push col.r |>.push col.g |>.push col.b |>.push col.a
        indices   := st.indices
        edgeCache := if slot < st.edgeCache.size then st.edgeCache.set! slot vid else st.edgeCache
        vertCount := vid + 1 }
    (st', vid)

private def pushOrientedTri (st : MtState) (i0 i1 i2 : UInt32) : MtState :=
  let o0 := i0.toNat * 3
  let o1 := i1.toNat * 3
  let o2 := i2.toNat * 3
  let p0 : Vec3 := ⟨st.positions.get! o0, st.positions.get! (o0 + 1), st.positions.get! (o0 + 2)⟩
  let p1 : Vec3 := ⟨st.positions.get! o1, st.positions.get! (o1 + 1), st.positions.get! (o1 + 2)⟩
  let p2 : Vec3 := ⟨st.positions.get! o2, st.positions.get! (o2 + 1), st.positions.get! (o2 + 2)⟩
  let n0 : Vec3 := ⟨st.normals.get! o0, st.normals.get! (o0 + 1), st.normals.get! (o0 + 2)⟩
  let n1 : Vec3 := ⟨st.normals.get! o1, st.normals.get! (o1 + 1), st.normals.get! (o1 + 2)⟩
  let n2 : Vec3 := ⟨st.normals.get! o2, st.normals.get! (o2 + 1), st.normals.get! (o2 + 2)⟩
  let faceN := Vec3.cross (Vec3.sub p1 p0) (Vec3.sub p2 p0)
  if Vec3.normSq faceN < 1e-18 then
    st -- Skip degenerate sliver triangles
  else
    let avgN := Vec3.add n0 (Vec3.add n1 n2)
    let idxs :=
      if Vec3.dot faceN avgN ≥ 0.0 then
        st.indices.push i0 |>.push i1 |>.push i2
      else
        st.indices.push i0 |>.push i2 |>.push i1
    { st with indices := idxs }

/-- Extract a watertight CCW `MeshAsset` of the zero-level isosurface `f(x, y, z) = iso`
over `[bmin, bmax]` at grid resolution `nx × ny × nz` using O(1) edge-cached Kuhn
Marching Tetrahedra. -/
def marchingTetrahedra (f : Vec3 → Float)
    (bmin bmax : Vec3) (nx ny nz : Nat) (meshId : UInt64)
    (iso : Float := 0.0) (gradEps : Float := 1.5e-3) : MeshAsset := Id.run do
  let nx' := max 4 (min 40 nx)
  let ny' := max 4 (min 40 ny)
  let nz' := max 4 (min 40 nz)
  let nx1 := nx' + 1
  let ny1 := ny' + 1
  let nz1 := nz' + 1
  let dx := (bmax.x - bmin.x) / Float.ofNat nx'
  let dy := (bmax.y - bmin.y) / Float.ofNat ny'
  let dz := (bmax.z - bmin.z) / Float.ofNat nz'
  -- Step 1: Sample scalar field on the (nx+1)*(ny+1)*(nz+1) grid once
  let totalPts := nx1 * ny1 * nz1
  let mut field := FloatArray.emptyWithCapacity totalPts
  for iz in [:nz1] do
    let z := bmin.z + Float.ofNat iz * dz
    for iy in [:ny1] do
      let y := bmin.y + Float.ofNat iy * dy
      for ix in [:nx1] do
        let x := bmin.x + Float.ofNat ix * dx
        field := field.push (f ⟨x, y, z⟩ - iso)
  let valAt (ix iy iz : Nat) : Float :=
    field.get! ((iz * ny1 + iy) * nx1 + ix)
  let posAt (ix iy iz : Nat) : Vec3 :=
    ⟨bmin.x + Float.ofNat ix * dx, bmin.y + Float.ofNat iy * dy, bmin.z + Float.ofNat iz * dz⟩
  -- Step 2: Traverse cells with O(1) empty-cell rejection & O(1) Kuhn edge vertex cache
  let mut st : MtState :=
    { positions := FloatArray.emptyWithCapacity 4096
      normals   := FloatArray.emptyWithCapacity 4096
      colors    := FloatArray.emptyWithCapacity 4096
      indices   := Array.mkEmpty 8192
      edgeCache := Array.replicate (totalPts * 7) 0xFFFFFFFF
      vertCount := 0 }
  for iz in [:nz'] do
    for iy in [:ny'] do
      for ix in [:nx'] do
        let v0 := valAt ix       iy       iz
        let v1 := valAt (ix + 1) iy       iz
        let v2 := valAt ix       (iy + 1) iz
        let v3 := valAt (ix + 1) (iy + 1) iz
        let v4 := valAt ix       iy       (iz + 1)
        let v5 := valAt (ix + 1) iy       (iz + 1)
        let v6 := valAt ix       (iy + 1) (iz + 1)
        let v7 := valAt (ix + 1) (iy + 1) (iz + 1)
        let b0 := v0 < 0.0; let b1 := v1 < 0.0; let b2 := v2 < 0.0; let b3 := v3 < 0.0
        let b4 := v4 < 0.0; let b5 := v5 < 0.0; let b6 := v6 < 0.0; let b7 := v7 < 0.0
        let allIn  := b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7
        let allOut := !b0 && !b1 && !b2 && !b3 && !b4 && !b5 && !b6 && !b7
        if !allIn && !allOut then
          let cornerIx (c : Nat) : Nat := ix + (c &&& 1)
          let cornerIy (c : Nat) : Nat := iy + ((c >>> 1) &&& 1)
          let cornerIz (c : Nat) : Nat := iz + ((c >>> 2) &&& 1)
          let cornerV (c : Nat) : Float :=
            match c with
            | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3
            | 4 => v4 | 5 => v5 | 6 => v6 | _ => v7
          for (c0, c1, c2, c3) in kuhnTets do
            let cs := #[c0, c1, c2, c3]
            let mut ins : Array Nat := #[]
            let mut outs : Array Nat := #[]
            for c in cs do
              if cornerV c < 0.0 then ins := ins.push c else outs := outs.push c
            let emitEdge (s : MtState) (a b : Nat) : MtState × UInt32 :=
              let ax := cornerIx a; let ay := cornerIy a; let az := cornerIz a
              let bx := cornerIx b; let by_ := cornerIy b; let bz := cornerIz b
              emitEdgeVert s f gradEps nx1 ny1 ax ay az (posAt ax ay az) (cornerV a)
                                               bx by_ bz (posAt bx by_ bz) (cornerV b)
            if ins.size == 1 && outs.size == 3 then
              let a := ins[0]!
              let (s1, i0) := emitEdge st a outs[0]!
              let (s2, i1) := emitEdge s1 a outs[1]!
              let (s3, i2) := emitEdge s2 a outs[2]!
              st := pushOrientedTri s3 i0 i1 i2
            else if ins.size == 3 && outs.size == 1 then
              let a := outs[0]!
              let (s1, i0) := emitEdge st a ins[0]!
              let (s2, i1) := emitEdge s1 a ins[1]!
              let (s3, i2) := emitEdge s2 a ins[2]!
              st := pushOrientedTri s3 i0 i1 i2
            else if ins.size == 2 && outs.size == 2 then
              let a := ins[0]!; let b := ins[1]!
              let c := outs[0]!; let d := outs[1]!
              let (s1, q0) := emitEdge st a c
              let (s2, q1) := emitEdge s1 a d
              let (s3, q2) := emitEdge s2 b d
              let (s4, q3) := emitEdge s3 b c
              let s5 := pushOrientedTri s4 q0 q1 q2
              st := pushOrientedTri s5 q0 q2 q3
  let h := meshHash meshId st.positions st.indices
  { meshId, dirtyHash := h, positions := st.positions, normals := st.normals,
    colors := st.colors, indices := st.indices }

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
  let f (p : Vec3) : Float :=
    let x := p.x * freq; let y := p.y * freq; let z := p.z * freq
    let g := Float.sin x * Float.cos y + Float.sin y * Float.cos z + Float.sin z * Float.cos x - iso
    -- Soft spherical bounding shell so Gyroid floats cleanly as a closed organic sculpture
    let r2 := p.x * p.x + p.y * p.y + p.z * p.z
    let mask := r2 - 1.75
    if mask > g then mask else g
  marchingTetrahedra f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Schwarz P** triply periodic minimal surface: `cos(kx) + cos(ky) + cos(kz) = iso`. -/
def buildSchwarzPMesh (iso : Float := 0.0) (freq : Float := 2.35) (gridN : Nat := 18)
    (meshId : UInt64 := 3002) : MeshAsset :=
  let f (p : Vec3) : Float :=
    let x := p.x * freq; let y := p.y * freq; let z := p.z * freq
    let s := Float.cos x + Float.cos y + Float.cos z - iso
    let r2 := p.x * p.x + p.y * p.y + p.z * p.z
    let mask := r2 - 1.85
    if mask > s then mask else s
  marchingTetrahedra f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Animated 4-Lobe Organic Metaballs**: `1.0 - ∑ rᵢ² / (‖p - cᵢ(t)‖² + 0.04) = 0`.
`ctrl` moves lobe 0 interactively! -/
def buildMetaballsMesh (t : Float) (ctrl : Vec3 := ⟨0.55, 0.25, 0.0⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 3003) : MeshAsset :=
  let c0 := ctrl
  let c1 : Vec3 := ⟨-0.58 * Float.cos (t * 0.9), 0.42 * Float.sin (t * 1.1), 0.35 * Float.sin (t * 0.7)⟩
  let c2 : Vec3 := ⟨0.32 * Float.sin (t * 1.3), -0.52 * Float.cos (t * 0.8), -0.40 * Float.cos (t * 1.0)⟩
  let c3 : Vec3 := ⟨-0.25 * Float.sin (t * 0.6), -0.20 * Float.sin (t * 1.2), 0.55 * Float.cos (t * 0.85)⟩
  let f (p : Vec3) : Float :=
    let d0 := Vec3.normSq (Vec3.sub p c0) + 0.04
    let d1 := Vec3.normSq (Vec3.sub p c1) + 0.04
    let d2 := Vec3.normSq (Vec3.sub p c2) + 0.04
    let d3 := Vec3.normSq (Vec3.sub p c3) + 0.04
    1.0 - (0.20 / d0 + 0.18 / d1 + 0.16 / d2 + 0.15 / d3)
  marchingTetrahedra f ⟨-1.45, -1.45, -1.45⟩ ⟨1.45, 1.45, 1.45⟩ gridN gridN gridN meshId

/-- **Genus-2 Double-Torus Pretzel**: `((x² + y²)² - x² + y²)² + z² - r² = 0`. -/
def buildGenus2Mesh (tubeR : Float := 0.22) (gridN : Nat := 20)
    (meshId : UInt64 := 3004) : MeshAsset :=
  let r2 := tubeR * tubeR
  let f (p : Vec3) : Float :=
    let x2 := p.x * p.x; let y2 := p.y * p.y; let z2 := p.z * p.z
    let q := (x2 + y2) * (x2 + y2) - x2 + y2
    q * q + z2 - r2
  marchingTetrahedra f ⟨-1.35, -1.0, -0.55⟩ ⟨1.35, 1.0, 0.55⟩ gridN gridN (max 10 (gridN / 2)) meshId

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
