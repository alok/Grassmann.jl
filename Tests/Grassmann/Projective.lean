/-
`grassmann/projective`: tests for `Grassmann.GanjaCompat` (arbitrary `Cl(p,q,r)`, Poincaré
duality, Dorst left contraction `<<`, Clifford conjugate vs reverse, Witt↔raw CGA vector bridge)
and `Grassmann.Projective` (PGA2/PGA3 points, Plücker lines, planes, join/meet, orthogonal
projection, closed-form `motorExp`/`motorLog`/SLERP, Study normalization, `motorToMat4`,
`transformXYZBatch`, rigid-body RK4 energy/Study conservation, and exact PGA3 triangle-mesh
plane slicing + 2D contour stitching).
-/
import Tests.Grassmann.Common
import Grassmann.Projective
import Grassmann.Kernel.Generated.R3
import Grassmann.Kernel.Generated.STA
import Grassmann.Kernel.Generated.CGA3

open Grassmann DirectSum StaticVectors Grassmann.GanjaCompat Grassmann.Projective

namespace GrassmannTests.ProjectiveSuite

/-- Close in absolute-or-relative terms. -/
def near (a b : Float) (tol : Float := 1e-9) : Bool :=
  (a - b).abs ≤ tol * (1.0 + a.abs + b.abs)

/-- 3D tuple nearness. -/
def near3 (a b : Float × Float × Float) (tol : Float := 1e-8) : Bool :=
  near a.1 b.1 tol && near a.2.1 b.2.1 tol && near a.2.2 b.2.2 tol

/-- Random eighth-grid float in `[-3, 3]`. -/
def randF : Tests.Gen Float := do
  let k ← Tests.Gen.int (-24) 24
  return k.toFloat / 8.0

/-- Random non-zero 3D unit vector. -/
def randUnit3 : Tests.Gen (Float × Float × Float) := do
  let x ← randF; let y ← randF; let z ← randF
  let n := Float.sqrt (x * x + y * y + z * z)
  if n < 1e-3 then return (0.0, 0.0, 1.0)
  else return (x / n, y / n, z / n)

/-- Rodrigues rotation of `(x, y, z)` around unit axis `(kx, ky, kz)` by `θ`. -/
def rodrigues (kx ky kz θ x y z : Float) : Float × Float × Float :=
  let c := Float.cos θ; let s := Float.sin θ
  let dot := kx * x + ky * y + kz * z
  let cx := ky * z - kz * y; let cy := kz * x - kx * z; let cz := kx * y - ky * x
  (c * x + s * cx + (1.0 - c) * dot * kx,
   c * y + s * cy + (1.0 - c) * dot * ky,
   c * z + s * cz + (1.0 - c) * dot * kz)

/-- Apply a column-major 4×4 affine matrix (`FloatArray` of length 16) to `(x, y, z)`. -/
def applyMat4 (m : FloatArray) (x y z : Float) : Float × Float × Float :=
  (m.get! 0 * x + m.get! 4 * y + m.get! 8  * z + m.get! 12,
   m.get! 1 * x + m.get! 5 * y + m.get! 9  * z + m.get! 13,
   m.get! 2 * x + m.get! 6 * y + m.get! 10 * z + m.get! 14)

/-- Closed CCW unit cube `[-1, 1]³` (8 vertices, 12 triangles). -/
def unitCubeMesh : FloatArray × Array UInt32 :=
  let verts : List Float :=
    [ -1, -1, -1,   1, -1, -1,   1,  1, -1,  -1,  1, -1,
      -1, -1,  1,   1, -1,  1,   1,  1,  1,  -1,  1,  1 ]
  let pos := verts.foldl FloatArray.push (FloatArray.emptyWithCapacity 24)
  let idx : Array UInt32 := #[
    -- -z face (0,3,2), (0,2,1)
    0, 3, 2,  0, 2, 1,
    -- +z face (4,5,6), (4,6,7)
    4, 5, 6,  4, 6, 7,
    -- -y face (0,1,5), (0,5,4)
    0, 1, 5,  0, 5, 4,
    -- +y face (3,7,6), (3,6,2)
    3, 7, 6,  3, 6, 2,
    -- -x face (0,4,7), (0,7,3)
    0, 4, 7,  0, 7, 3,
    -- +x face (1,2,6), (1,6,5)
    1, 2, 6,  1, 6, 5
  ]
  (pos, idx)

/-- Check `GanjaCompat`: `cl p q r`, Poincaré dual, Dorst `<<`, conjugate, Witt↔raw CGA. -/
def checkGanjaCompat : Tests.Gen Tally := do
  let mut t : Tally := {}
  -- 1. TensorBundle.cl p q r signatures
  t := t.check (TensorBundle.cl 2 0 1 == PGA2) "cl 2 0 1 = PGA2"
  t := t.check (TensorBundle.cl 3 0 1 == PGA3) "cl 3 0 1 = PGA3"
  t := t.check (TensorBundle.cl 3 0 0 == S!"+++") "cl 3 0 0 = S!\"+++\""
  t := t.check (TensorBundle.cl 4 1 0 == S!"++++-") "cl 4 1 0 = S!\"++++-\""
  t := t.check (TensorBundle.cl 3 1 0 == S!"+++-") "cl 3 1 0 = S!\"+++-\""
  t := t.check (TensorBundle.cl 0 1 0 == S!"-") "cl 0 1 0 = S!\"-\""
  t := t.check (TensorBundle.cl 0 2 0 == S!"--") "cl 0 2 0 = S!\"--\""
  t := t.check (TensorBundle.cl 0 0 1 == D!"0") "cl 0 0 1 = D!\"0\""
  t := t.check (TensorBundle.cl 1 3 0 == S!"+---") "cl 1 3 0 = S!\"+---\""
  -- 2. Poincaré dual roundtrip in PGA3 (metric-free: !e0 = e123 ≠ 0!)
  let e0 : Plane3 := mkPlane3 0.0 0.0 0.0 1.0
  let de0 : Point3 := dualChain e0
  t := t.check (near (de0.v.get! 3) 1.0) "PGA3 dualChain e0 = e123 (non-zero!)"
  let rt0 : Plane3 := undualChain de0
  t := t.check (near (rt0.v.get! 0) 1.0) "PGA3 undualChain (dualChain e0) = e0"
  -- 3. Dorst left contraction `dorstLDotChain` equals `gradePart (a * b) (H - G)` across grades!
  for _ in [0:15] do
    let a1 : Chain ℝ3 1 Float := ⟨Values.ofFn fun _ => 0.0⟩
    let _ := a1
    let x1 ← randF; let y1 ← randF; let z1 ← randF
    let x2 ← randF; let y2 ← randF; let z2 ← randF
    let u : Chain ℝ3 1 Float := (Chain.ofList? [x1, y1, z1]).get!
    let v : Chain ℝ3 1 Float := (Chain.ofList? [x2, y2, z2]).get!
    let b : Chain ℝ3 2 Float := u ∧ v
    let tri : Chain ℝ3 3 Float := (Chain.ofList? [x1 + 0.5]).get!
    -- grade 1 ⌋ grade 2
    let l12 : Chain ℝ3 1 Float := dorstLDotChain u b
    let ref12 : Chain ℝ3 1 Float := (u * b).grade 1
    t := t.check ((List.range 3).all fun i => near (l12.v.get! i) (ref12.v.get! i))
      "ℝ3 dorstLDotChain (1, 2) = ⟨u*b⟩₁"
    -- grade 2 ⌋ grade 2 (crucial test: flips sign vs Grassmann.jl `contraction`!)
    let l22 : Chain ℝ3 0 Float := dorstLDotChain b b
    let ref22 : Chain ℝ3 0 Float := (b * b).grade 0
    t := t.check (near (l22.v.get! 0) (ref22.v.get! 0))
      "ℝ3 dorstLDotChain (2, 2) = ⟨b*b⟩₀ (negative definite!)"
    -- grade 2 ⌋ grade 3 (also flips sign vs Grassmann.jl `<`)
    let l23 : Chain ℝ3 1 Float := dorstLDotChain b tri
    let ref23 : Chain ℝ3 1 Float := (b * tri).grade 1
    t := t.check ((List.range 3).all fun i => near (l23.v.get! i) (ref23.v.get! i))
      "ℝ3 dorstLDotChain (2, 3) = ⟨b*I⟩₁"
    -- grade 3 ⌋ grade 3
    let l33 : Chain ℝ3 0 Float := dorstLDotChain tri tri
    let ref33 : Chain ℝ3 0 Float := (tri * tri).grade 0
    t := t.check (near (l33.v.get! 0) (ref33.v.get! 0))
      "ℝ3 dorstLDotChain (3, 3) = ⟨I*I⟩₀"
    -- Clifford conjugate vs reverse signs: [+, -, -, +] vs [+, +, -, -]
    t := t.check (near ((conjChain u).v.get! 0) (-(u.v.get! 0))) "conjChain flips grade 1"
    t := t.check (near ((revChain u).v.get! 0) (u.v.get! 0)) "revChain keeps grade 1"
    t := t.check (near ((conjChain b).v.get! 0) (-(b.v.get! 0))) "conjChain flips grade 2"
    t := t.check (near ((conjChain tri).v.get! 0) (tri.v.get! 0)) "conjChain keeps grade 3"
    t := t.check (near ((revChain tri).v.get! 0) (-(tri.v.get! 0))) "revChain flips grade 3"
  -- 4. Witt ↔ raw CGA3 vector round-trip & dot product isometry
  for _ in [0:15] do
    let ci ← randF; let co ← randF; let x ← randF; let y ← randF; let z ← randF
    let vw : Chain (cgaWitt 3) 1 Float := (Chain.ofList? [ci, co, x, y, z]).get!
    let vr := cgaWittToRawVec vw
    let vw' := cgaRawToWittVec vr
    t := t.check ((List.range 5).all fun i => near (vw.v.get! i) (vw'.v.get! i))
      "CGA3 Witt↔raw roundtrip"
    -- Inner product isometry: -2*ci*co + x²+y²+z² == x²+y²+z² + c₊² - c₋²
    let dotW := -2.0 * ci * co + x * x + y * y + z * z
    let dotR := vr.v.get! 0 * vr.v.get! 0 + vr.v.get! 1 * vr.v.get! 1 + vr.v.get! 2 * vr.v.get! 2 +
                vr.v.get! 3 * vr.v.get! 3 - vr.v.get! 4 * vr.v.get! 4
    t := t.check (near dotW dotR) "CGA3 Witt↔raw dot product isometry"
  return t

/-- Check PGA2 geometry & Wedge 2D operations. -/
def checkPGA2 : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:20] do
    let x1 ← randF; let y1 ← randF
    let x2 ← randF; let y2 ← randF
    let p1 := mkPoint2 x1 y1
    let p2 := mkPoint2 x2 y2
    match point2Coords? p1 with
    | some (rx, ry) => t := t.check (near rx x1 && near ry y1) "PGA2 point roundtrip"
    | none => t := t.bad "PGA2 point coords none"
    -- Join two distinct points -> line passing through both
    if (x1 - x2).abs + (y1 - y2).abs > 0.25 then
      let l := normalizeLine2 (joinPoints2 p1 p2)
      let c := l.v.get! 0; let a := l.v.get! 1; let b := l.v.get! 2
      t := t.check (near (a * x1 + b * y1 + c) 0.0 1e-8 && near (a * x2 + b * y2 + c) 0.0 1e-8)
        "PGA2 joinPoints2 incidence"
      -- Orthogonal line through p3: perpendicular to l and passing through p3
      let x3 ← randF; let y3 ← randF
      let p3 := mkPoint2 x3 y3
      let lo := normalizeLine2 (orthoLineThrough2 l p3)
      let co := lo.v.get! 0; let ao := lo.v.get! 1; let bo := lo.v.get! 2
      t := t.check (near (a * ao + b * bo) 0.0 1e-8 && near (ao * x3 + bo * y3 + co) 0.0 1e-8)
        "PGA2 orthoLineThrough2 (L << P) perpendicular and incident"
      -- Meet l and lo -> foot of p3 on l
      match point2Coords? (meetLines2 l lo) with
      | some (fx, fy) =>
        t := t.check (near (a * fx + b * fy + c) 0.0 1e-7 && near (ao * fx + bo * fy + co) 0.0 1e-7)
          "PGA2 meetLines2 lies on both lines"
      | none => t := t.bad "PGA2 perpendicular lines meet none"
  -- 2D rotor (90° CCW around origin: (1,0) -> (0,1)) & translator
  let r90 := rotor2 0.0 0.0 (Float.acos (-1.0) / 2.0)
  match point2Coords? (applyMotor2Point r90 (mkPoint2 1.0 0.0)) with
  | some (x, y) => t := t.check (near x 0.0 1e-9 && near y 1.0 1e-9) "PGA2 rotor2 90° CCW"
  | none => t := t.bad "PGA2 rotor2 none"
  let rPivot := rotor2 2.0 (-1.0) (Float.acos (-1.0) / 2.0)
  match point2Coords? (applyMotor2Point rPivot (mkPoint2 3.0 (-1.0))) with
  | some (x, y) => t := t.check (near x 2.0 1e-9 && near y 0.0 1e-9) "PGA2 rotor2 off-origin pivot 90° CCW"
  | none => t := t.bad "PGA2 rotor2 pivot none"
  let tr := translator2 2.5 (-1.25)
  match point2Coords? (applyMotor2Point tr (mkPoint2 1.0 3.0)) with
  | some (x, y) => t := t.check (near x 3.5 1e-9 && near y 1.75 1e-9) "PGA2 translator2"
  | none => t := t.bad "PGA2 translator2 none"
  return t

/-- Check PGA3 geometry, closed-form motors, Study normalization, 4×4 matrix & batch transforms. -/
def checkPGA3Motors : Tests.Gen Tally := do
  let mut t : Tally := {}
  -- Basic point/line/plane joins & meets
  let pA := mkPoint3 1.0 0.0 0.0
  let pB := mkPoint3 0.0 1.0 0.0
  let pC := mkPoint3 0.0 0.0 1.0
  let pl := normalizePlane3 (join3Points3 pA pB pC)
  t := t.check (near (signedDistPlanePoint pl 1.0 0.0 0.0) 0.0 1e-9 &&
                near (signedDistPlanePoint pl 0.0 1.0 0.0) 0.0 1e-9 &&
                near (signedDistPlanePoint pl 0.0 0.0 1.0) 0.0 1e-9)
    "PGA3 join3Points3 plane passes through all 3 points"
  -- Meet 3 coordinate planes x=2, y=-3, z=4 -> (2, -3, 4)
  let px := mkPlane3 1.0 0.0 0.0 (-2.0)
  let py := mkPlane3 0.0 1.0 0.0 3.0
  let pz := mkPlane3 0.0 0.0 1.0 (-4.0)
  match point3Coords? (meet3Planes3 px py pz) with
  | some c => t := t.check (near3 c (2.0, -3.0, 4.0) 1e-9) "PGA3 meet3Planes3 = (2,-3,4)"
  | none => t := t.bad "PGA3 meet3Planes3 none"
  -- Plücker line extraction
  let lAB := joinPoints3 (mkPoint3 1.0 2.0 3.0) (mkPoint3 1.0 2.0 7.0)
  match line3OriginDir? lAB with
  | some (orig, dir) =>
    t := t.check (near3 orig (1.0, 2.0, 0.0) 1e-9 && (near3 dir (0.0, 0.0, 1.0) 1e-9 || near3 dir (0.0, 0.0, -1.0) 1e-9))
      "PGA3 line3OriginDir? recovers closest point & axis"
  | none => t := t.bad "PGA3 line3OriginDir? none"
  -- Plane frame orthonormality
  match plane3Frame? pl with
  | some ((ox, oy, oz), (ux, uy, uz), (vx, vy, vz)) =>
    let nx := pl.v.get! 1; let ny := pl.v.get! 2; let nz := pl.v.get! 3
    t := t.check (near (signedDistPlanePoint pl ox oy oz) 0.0 1e-9) "plane3Frame? origin on plane"
    t := t.check (near (ux * ux + uy * uy + uz * uz) 1.0 1e-9 &&
                  near (vx * vx + vy * vy + vz * vz) 1.0 1e-9 &&
                  near (ux * vx + uy * vy + uz * vz) 0.0 1e-9 &&
                  near3 (uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx) (nx, ny, nz) 1e-9)
      "plane3Frame? orthonormal right-handed basis u × v = n"
  | none => t := t.bad "plane3Frame? none"
  -- Random rotor3 vs Rodrigues, translator3, motorExp/motorLog/SLERP, Study norm, motorToMat4, batch
  for _ in [0:40] do
    let (kx, ky, kz) ← randUnit3
    let angle ← randF
    let px ← randF; let py ← randF; let pz ← randF
    let dx ← randF; let dy ← randF; let dz ← randF
    -- rotor3 vs Rodrigues
    let r := rotor3 kx ky kz angle
    let expected := rodrigues kx ky kz angle px py pz
    match point3Coords? (applyMotor3Point r (mkPoint3 px py pz)) with
    | some got => t := t.check (near3 got expected 1e-8) "PGA3 rotor3 matches Rodrigues"
    | none => t := t.bad "PGA3 rotor3 point none"
    -- translator3
    let tr := translator3 dx dy dz
    match point3Coords? (applyMotor3Point tr (mkPoint3 px py pz)) with
    | some got => t := t.check (near3 got (px + dx, py + dy, pz + dz) 1e-9) "PGA3 translator3"
    | none => t := t.bad "PGA3 translator3 none"
    -- General composite screw motor M = tr * r
    let m : Motor3 := tr * r
    t := t.check (motorIsValid m 1e-9) "composite T*R satisfies Study condition"
    -- Perturb M off Study quadric and verify normalizeMotor3 restores M * ~M = 1
    let noisy : Motor3 :=
      ⟨Values.ofFn fun i => m.v.get i * 1.7 + (if i.1 == 7 then 0.35 else if i.1 == 1 then 0.12 else 0.0)⟩
    let nm := normalizeMotor3 noisy
    let prod : Motor3 := nm * ~nm
    t := t.check (near (prod.v.get! 0) 1.0 1e-9 && near (prod.v.get! 7) 0.0 1e-9 && motorIsValid nm 1e-9)
      "normalizeMotor3 restores M * ~M = 1"
    -- motorExp (motorLog m) == ±m
    let bLog := motorLog m
    let mRec := motorExp bLog
    let sgn := if m.v.get! 0 * mRec.v.get! 0 + m.v.get! 4 * mRec.v.get! 4 +
                  m.v.get! 5 * mRec.v.get! 5 + m.v.get! 6 * mRec.v.get! 6 < 0.0 then -1.0 else 1.0
    t := t.check ((List.range 8).all fun i => near (mRec.v.get! i) (sgn * m.v.get! i) 1e-7)
      "PGA3 motorExp (motorLog M) = ±M"
    -- motorExp matches exact 24-term Taylor series ∑ B^k / k! on general screw bivector B
    let b01 ← randF; let b02 ← randF; let b03 ← randF
    let b12 := 0.3 * (← randF); let b13 := 0.3 * (← randF); let b23 := 0.3 * (← randF)
    let biv : Line3 := (Chain.ofList? [b01, b02, b03, b12, b13, b23]).get!
    let mFast := motorExp biv
    let bivM : Motor3 := line3ToMotor3 biv
    let mut sumM : Motor3 := identityMotor3
    let mut termM : Motor3 := identityMotor3
    for k in [1:25] do
      termM := (1.0 / k.toFloat) • (termM * bivM : Motor3)
      sumM := sumM + termM
    t := t.check ((List.range 8).all fun i => near (mFast.v.get! i) (sumM.v.get! i) 1e-10)
      "PGA3 motorExp matches exact 24-term Taylor series"
    -- bivectorSplit: B = B_rot + B_trans, [B_rot, B_trans] = 0, B_rot² scalar, B_trans² = 0,
    -- and exp(B) = exp(B_rot) * exp(B_trans)
    let (brot, btr) := bivectorSplit biv
    let comm := bivectorCommutator brot btr
    let brotM := line3ToMotor3 brot
    let btrM := line3ToMotor3 btr
    let brotSq : Motor3 := brotM * brotM
    let btrSq : Motor3 := btrM * btrM
    let mSplit : Motor3 := motorExp brot * motorExp btr
    t := t.check ((List.range 6).all fun i =>
        near (brot.v.get! i + btr.v.get! i) (biv.v.get! i) 1e-9 && near (comm.v.get! i) 0.0 1e-8)
      "PGA3 bivectorSplit sums to B and commutes"
    t := t.check (near (brotSq.v.get! 7) 0.0 1e-8 &&
        (List.range 8).all fun i => near (btrSq.v.get! i) 0.0 1e-9 &&
          near (mSplit.v.get! i) (mFast.v.get! i) 1e-8)
      "PGA3 bivectorSplit yields pure rotation + pure translation and exp(B)=exp(Br)*exp(Bt)"
    -- motorToMat4 & transformXYZBatch match M >>> P exactly!
    let mat := motorToMat4 m
    let gotMat := applyMat4 mat px py pz
    match point3Coords? (applyMotor3Point m (mkPoint3 px py pz)) with
    | some gotGA =>
      t := t.check (near3 gotMat gotGA 1e-8) "PGA3 motorToMat4 matches M >>> P"
      let batchIn := (((((FloatArray.emptyWithCapacity 6).push px).push py).push pz).push 0.0).push 0.0 |>.push 0.0
      let batchOut := transformXYZBatch m batchIn
      t := t.check (near3 (batchOut.get! 0, batchOut.get! 1, batchOut.get! 2) gotGA 1e-8)
        "PGA3 transformXYZBatch matches M >>> P"
    | none => t := t.bad "PGA3 M >>> P none"
    -- SLERP endpoints & midpoint norm
    let mMid := motorSlerp identityMotor3 m 0.5
    t := t.check (motorIsValid mMid 1e-8) "PGA3 motorSlerp midpoint valid"
    let mMid2 : Motor3 := mMid * mMid
    let sgn2 := if m.v.get! 0 * mMid2.v.get! 0 + m.v.get! 4 * mMid2.v.get! 4 +
                   m.v.get! 5 * mMid2.v.get! 5 + m.v.get! 6 * mMid2.v.get! 6 < 0.0 then -1.0 else 1.0
    t := t.check ((List.range 8).all fun i => near (mMid2.v.get! i) (sgn2 * m.v.get! i) 1e-6)
      "PGA3 (motorSlerp 1 M 0.5)² = ±M"
  return t

/-- Check rigid-body RK4 dynamics (energy & Study norm conservation) and PGA3 mesh slicing. -/
def checkPhysicsAndSlicing : Tests.Gen Tally := do
  let mut t : Tally := {}
  -- 1. Torque-free asymmetric rigid body (Dzhanibekov / free top): conserves kinetic energy & Study motor!
  let zeroForque : Motor3 → Line3 → Line3 := fun _ _ => Chain.zero
  let initVel : Line3 := (Chain.ofList? [0.2, -0.1, 0.3, 0.5, 1.4, 0.3]).get!
  let rb0 : RigidBody3 := { motor := identityMotor3, vel := initVel, mass := 2.0, ix := 1.0, iy := 2.0, iz := 3.5 }
  let e0 := rigidBodyKineticEnergy rb0
  let mut rb := rb0
  for _ in [0:200] do
    rb := rigidBodyStepRK4 rb zeroForque 0.01
  let e1 := rigidBodyKineticEnergy rb
  t := t.check (near e0 e1 1e-6) s!"PGA3 free top conserves kinetic energy ({e0} vs {e1})"
  t := t.check (motorIsValid rb.motor 1e-9) "PGA3 free top preserves Study motor invariant"
  -- Pack/unpack roundtrip
  let packed := rigidBodyPack rb
  let (mU, vU) := rigidBodyUnpack packed
  t := t.check (packed.size == 14 &&
                (List.range 8).all (fun i => near (mU.v.get! i) (rb.motor.v.get! i)) &&
                (List.range 6).all (fun i => near (vU.v.get! i) (rb.vel.v.get! i)))
    "PGA3 rigidBodyPack/Unpack roundtrip"
  -- 2. Exact PGA3 mesh slicing on closed unit cube [-1, 1]³
  let (cubePos, cubeIdx) := unitCubeMesh
  -- 2a. Horizontal slice z = 0.25 (plane z - 0.25 = 0)
  let plZ := mkPlane3 0.0 0.0 1.0 (-0.25)
  let resZ := sliceMeshByPlane cubePos cubeIdx plZ
  t := t.check (resZ.posHalf.indices.size > 0 && resZ.negHalf.indices.size > 0)
    "cube slice z=0.25 produces non-empty pos and neg half-meshes"
  -- Every vertex in posHalf has z ≥ 0.25 - eps; every vertex in negHalf has z ≤ 0.25 + eps
  let posOk := (List.range (resZ.posHalf.positions.size / 3)).all fun k =>
    resZ.posHalf.positions.get! (3 * k + 2) ≥ 0.25 - 1e-6
  let negOk := (List.range (resZ.negHalf.positions.size / 3)).all fun k =>
    resZ.negHalf.positions.get! (3 * k + 2) ≤ 0.25 + 1e-6
  t := t.check (posOk && negOk) "cube slice z=0.25 respects half-space bounds"
  -- Stitched 2D contour should be 1 closed square loop of perimeter 8.0
  t := t.check (resZ.contourPolylines2D.size == 1) "cube slice z=0.25 stitches into 1 closed contour loop"
  if h : 0 < resZ.contourPolylines2D.size then
    let poly := resZ.contourPolylines2D[0]'h
    let nPts := poly.size / 2
    let mut perim := 0.0
    for k in [0:nPts - 1] do
      let dx := poly.get! (2 * (k + 1)) - poly.get! (2 * k)
      let dy := poly.get! (2 * (k + 1) + 1) - poly.get! (2 * k + 1)
      perim := perim + Float.sqrt (dx * dx + dy * dy)
    let closed := near (poly.get! 0) (poly.get! (2 * (nPts - 1))) 1e-5 &&
                  near (poly.get! 1) (poly.get! (2 * (nPts - 1) + 1)) 1e-5
    t := t.check (closed && near perim 8.0 1e-4) s!"cube slice z=0.25 square contour perimeter = 8 ({perim})"
  -- 2b. Tilted diagonal plane x + y + z = 0 -> regular hexagon contour (perimeter = 6 * √2)
  let plDiag := mkPlane3 1.0 1.0 1.0 0.0
  let resD := sliceMeshByPlane cubePos cubeIdx plDiag
  t := t.check (resD.contourPolylines2D.size == 1) "cube slice x+y+z=0 stitches into 1 hexagonal loop"
  if h : 0 < resD.contourPolylines2D.size then
    let poly := resD.contourPolylines2D[0]'h
    let nPts := poly.size / 2
    let mut perim := 0.0
    for k in [0:nPts - 1] do
      let dx := poly.get! (2 * (k + 1)) - poly.get! (2 * k)
      let dy := poly.get! (2 * (k + 1) + 1) - poly.get! (2 * k + 1)
      perim := perim + Float.sqrt (dx * dx + dy * dy)
    let closed := near (poly.get! 0) (poly.get! (2 * (nPts - 1))) 1e-5 &&
                  near (poly.get! 1) (poly.get! (2 * (nPts - 1) + 1)) 1e-5
    t := t.check (closed && near perim (6.0 * Float.sqrt 2.0) 1e-4)
      s!"cube slice x+y+z=0 hexagon perimeter = 6√2 ({perim})"
  -- 2c. Non-intersecting plane z = 5.0
  let resMiss := sliceMeshByPlane cubePos cubeIdx (mkPlane3 0.0 0.0 1.0 (-5.0))
  t := t.check (resMiss.posHalf.indices.size == 0 && resMiss.negHalf.indices.size == 36 &&
                resMiss.contourPolylines2D.isEmpty)
    "non-intersecting slice keeps full mesh on negative side with 0 contours"
  return t

/-- Run the `grassmann/projective` suite. -/
def run : IO Tally := do
  let g : Tests.Gen Tally := do
    let t1 ← checkGanjaCompat
    let t2 ← checkPGA2
    let t3 ← checkPGA3Motors
    let t4 ← checkPhysicsAndSlicing
    return ((t1.merge t2).merge t3).merge t4
  return Tests.Gen.run 0x50474133 g

end GrassmannTests.ProjectiveSuite
