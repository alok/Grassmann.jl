/-
`grassmann/conformal`: the conformal-model utilities (`Grassmann.Conformal`) in
CGA2, CGA3 and CGA4, on random configurations (SplitMix64, fixed seed):
embedding round trips, incidence, spheres and planes through points recovering
their centre/radius/normal, point pairs of line–sphere meets, `dual`/`undual`,
translators, and the outermorphism of a versor agreeing with its sandwich.
-/
import Tests.Grassmann.Common
import Grassmann.Conformal

open Grassmann DirectSum StaticVectors Grassmann.Forms Grassmann.Conformal

namespace GrassmannTests.ConformalSuite

/-- Close in absolute-or-relative terms. -/
def near (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol * (1.0 + a.abs + b.abs)

/-- Coordinates close. -/
def nearL (xs ys : List Float) (tol : Float := 1e-9) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (a, b) => near a b tol

/-- Every coefficient of a multivector close to the other's. -/
def nearMV {V : TensorBundle} (a b : Multivector V Float) (tol : Float := 1e-9) : Bool :=
  nearL a.v.toList b.v.toList tol

/-- A random point with coordinates in `[-4, 4]` (eighths, so exact in Float). -/
def randPoint (d : Nat) : Tests.Gen (List Float) := do
  let xs ← Tests.Gen.array d (Tests.Gen.int (-32) 32)
  return xs.toList.map fun k => k.toFloat / 8.0

/-- Unit vector from random coordinates (falls back to `e₁`). -/
def unit (xs : List Float) : List Float :=
  let n := Float.sqrt (xs.foldl (fun a x => a + x * x) 0)
  if n < 1e-6 then 1.0 :: (xs.drop 1).map fun _ => 0.0 else xs.map (· / n)

/-- `d + 1` points on the sphere `(c, r)`: `c + r uᵢ` for random unit `uᵢ`. -/
def onSphere (c : List Float) (r : Float) (us : List (List Float)) : List (List Float) :=
  us.map fun u => (c.zip (unit u)).map fun (ci, ui) => ci + r * ui

set_option maxHeartbeats 2000000 in
/-- The checks for one conformal space of Euclidean dimension `d`. -/
def checks (V : TensorBundle) [Kernels V] (d : Nat) (name : String) (trials : Nat) :
    Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let x ← randPoint d
    let y ← randPoint d
    let c ← randPoint d
    let rk ← Tests.Gen.int 2 20
    let r := rk.toFloat / 4.0
    let X : CVec V := point (vec x)
    let Y : CVec V := point (vec y)
    -- embedding: null, unit weight, round trip, distances
    t := t.check (near (dot X X) 0) s!"{name}: up x is null"
    t := t.check (near (weight X) 1) s!"{name}: up x has unit weight"
    t := t.check (nearL ((down? ((3.5 : Float) • X)).map coords |>.getD []) x) s!"{name}: down (λ up x) = x"
    let d2 := (x.zip y).foldl (fun a (p, q) => a + (p - q) * (p - q)) 0
    t := t.check (near (distance2 X ((-2.0 : Float) • Y)) d2) s!"{name}: distance2 is scale-free"
    -- dual sphere: X⋅s = -½(|x-c|² - r²); centre/radius extraction
    let s : CVec V := dualSphere (vec c) r
    let dxc := (x.zip c).foldl (fun a (p, q) => a + (p - q) * (p - q)) 0
    t := t.check (near (dot X s) (-0.5 * (dxc - r * r))) s!"{name}: X⋅s = -½(|x-c|²-r²)"
    match sphereCenterRadius2? ((0.25 : Float) • s) with
    | some (cc, r2) => t := t.check (nearL (coords cc) c && near r2 (r * r)) s!"{name}: sphere centre/radius"
    | none => t := t.bad s!"{name}: sphere centre/radius none"
    -- sphere through d+1 points on (c, r)
    let us ← (List.range (d + 1)).mapM fun _ => randPoint d
    let pts := onSphere c r us
    match sphereThrough? (V := V) (pts.map vec) with
    | some s' =>
      match sphereCenterRadius2? s' with
      | some (cc, r2) =>
        t := t.check (nearL (coords cc) c 1e-6 && near r2 (r * r) 1e-6) s!"{name}: sphereThrough recovers (c, r)"
      | none => t := t.bad s!"{name}: sphereThrough flat"
      t := t.check (pts.all fun p => near (dot (point (V := V) (vec p)) s') 0 1e-6)
        s!"{name}: sphereThrough is incident with its points"
    | none => t := t.skip "degenerate random sphere points"
    -- plane through d points: every point incident, unit normal
    let ps ← (List.range d).mapM fun _ => randPoint d
    match planeThrough? (V := V) (ps.map vec) with
    | some π =>
      t := t.check (ps.all fun p => near (dot (point (V := V) (vec p)) π) 0 1e-6)
        s!"{name}: planeThrough is incident with its points"
      t := t.check (near (dot (euclidean π) (euclidean π)) 1) s!"{name}: planeThrough normal is unit"
    | none => t := t.skip "degenerate random plane points"
    -- line through c along u meets the sphere (c, r) at c ± r u
    let u := unit (← randPoint d)
    let p0 := (c.zip u).map fun (ci, ui) => ci - 3 * r * ui
    let p1 := (c.zip u).map fun (ci, ui) => ci + 3 * r * ui
    let L : Chain V 3 Float := (point (V := V) (vec p0) ∧ point (V := V) (vec p1)) ∧ inf V
    let T : Chain V 2 Float := L ⋅ s
    match pointPair? T with
    | some (a, b) =>
      let plus := (c.zip u).map fun (ci, ui) => ci + r * ui
      let minus := (c.zip u).map fun (ci, ui) => ci - r * ui
      let ok := (nearL (coords a) plus 1e-6 && nearL (coords b) minus 1e-6) ||
                (nearL (coords a) minus 1e-6 && nearL (coords b) plus 1e-6)
      t := t.check ok s!"{name}: line ∩ sphere = c ± r u"
    | none => t := t.bad s!"{name}: line through the centre misses the sphere"
    -- a line far outside misses: imaginary point pair
    let off := (c.zip u).map fun (ci, _) => ci + 10 * r
    let Lfar : Chain V 3 Float := (point (V := V) (vec off) ∧ point (V := V) (vec ((off.zip u).map fun (o, ui) => o + ui))) ∧ inf V
    t := t.check ((pointPair? (Lfar ⋅ s)).isNone ||
      -- (a random direction can still pass near; accept a real pair only if both points lie on s)
      (match pointPair? (Lfar ⋅ s) with
       | some (a, b) => near (dot (point (V := V) a) s) 0 1e-6 && near (dot (point (V := V) b) s) 0 1e-6
       | none => true)) s!"{name}: far line misses or hits on the sphere"
    -- dual/undual round trip on a random multivector
    let mv := (X ∧ Y).toMultivector + (s.toMultivector)
    t := t.check (nearMV (undual (dual mv)) mv) s!"{name}: undual ∘ dual = id"
    -- translator moves points and keeps spheres' radii
    let tv := (x.zip c).map fun (p, q) => p - q
    match ((translate (vec tv) X.toMultivector).grade 1 : CVec V) |> down? with
    | some z => t := t.check (nearL (coords z) ((x.zip tv).map fun (p, q) => p + q)) s!"{name}: translate moves points"
    | none => t := t.bad s!"{name}: translated point flat"
    match sphereCenterRadius2? ((translate (vec tv) s.toMultivector).grade 1) with
    | some (_, r2) => t := t.check (near r2 (r * r)) s!"{name}: translate keeps radius"
    | none => t := t.bad s!"{name}: translated sphere flat"
    -- the outermorphism of a versor is its sandwich on every grade, with det 1
    let R := translator (V := V) (vec tv)
    let O := Outermorphism.ofSimplex (versorMap R)
    let B : Chain V 2 Float := X ∧ Y
    let viaO : Chain V 2 Float := O.apply B
    let viaR := (R * B.toMultivector * ~R).grade 2
    t := t.check (nearL viaO.v.toList viaR.v.toList 1e-8) s!"{name}: outermorphism of versor = sandwich on bivectors"
    t := t.check (near O.det 1 1e-9) s!"{name}: det of a translator's outermorphism = 1"
  return t

/-- Tests for `interpreteCGA3` and `interpreteCGA2` round/flat classification and fast `FloatArray` helpers. -/
def checkInterprete : Tests.Gen Tally := do
  let mut t : Tally := {}
  -- 1. CGA3 point (OPNS grade 1 & flat point P ∧ ∞)
  let pA := point3 1.5 (-2.0) 0.75
  match interpreteCGA3 pA.toMultivector with
  | .point (x, y, z) =>
    t := t.check (near x 1.5 && near y (-2.0) && near z 0.75) "interpreteCGA3 grade-1 point"
  | _ => t := t.bad "interpreteCGA3 grade-1 point wrong kind"
  let flatP : Chain CGA3 2 Float := pA ∧ inf CGA3
  match interpreteCGA3 flatP.toMultivector with
  | .point (x, y, z) =>
    t := t.check (near x 1.5 && near y (-2.0) && near z 0.75) "interpreteCGA3 flat point P∧∞"
  | _ => t := t.bad "interpreteCGA3 flat point wrong kind"
  -- 2. Real point pair P1 ∧ P2
  let pB := point3 (-0.5) 1.0 2.25
  let pp : Chain CGA3 2 Float := pA ∧ pB
  match interpreteCGA3 pp.toMultivector with
  | .pointPair a b false =>
    let ok := (near a.1 1.5 1e-6 && near a.2.1 (-2.0) 1e-6 && near a.2.2 0.75 1e-6 &&
               near b.1 (-0.5) 1e-6 && near b.2.1 1.0 1e-6 && near b.2.2 2.25 1e-6) ||
              (near b.1 1.5 1e-6 && near b.2.1 (-2.0) 1e-6 && near b.2.2 0.75 1e-6 &&
               near a.1 (-0.5) 1e-6 && near a.2.1 1.0 1e-6 && near a.2.2 2.25 1e-6)
    t := t.check ok "interpreteCGA3 real pointPair"
  | _ => t := t.bad "interpreteCGA3 real pointPair wrong kind"
  -- 3. Imaginary point pair (line outside sphere)
  let sUnit := dualSphere3 0.0 0.0 0.0 1.0
  let lOut : Chain CGA3 3 Float := (point3 3.0 0.0 (-1.0) ∧ point3 3.0 0.0 1.0) ∧ inf CGA3
  let ppImag : Chain CGA3 2 Float := lOut ⋅ sUnit
  match interpreteCGA3 ppImag.toMultivector with
  | .pointPair a b true =>
    let cx := 0.5 * (a.1 + b.1); let cy := 0.5 * (a.2.1 + b.2.1); let cz := 0.5 * (a.2.2 + b.2.2)
    t := t.check (near cx 3.0 1e-6 && near cy 0.0 1e-6 && near cz 0.0 1e-6)
      "interpreteCGA3 imaginary pointPair centered at (3,0,0)"
  | _ => t := t.bad "interpreteCGA3 imaginary pointPair wrong kind"
  -- 4. Line P1 ∧ P2 ∧ ∞ (axis-aligned + 10 random 3D lines)
  let lineZ : Chain CGA3 3 Float := (point3 1.0 2.0 (-1.0) ∧ point3 1.0 2.0 3.0) ∧ inf CGA3
  match interpreteCGA3 lineZ.toMultivector with
  | .line (ox, oy, oz) (dx, dy, dz) =>
    t := t.check (near ox 1.0 1e-6 && near oy 2.0 1e-6 && near oz 0.0 1e-6 &&
                  near dx 0.0 1e-6 && near dy 0.0 1e-6 && near dz.abs 1.0 1e-6)
      "interpreteCGA3 OPNS line"
  | _ => t := t.bad "interpreteCGA3 OPNS line wrong kind"
  for _ in [0:10] do
    let a ← randPoint 3; let b ← randPoint 3
    let ax := a[0]!; let ay := a[1]!; let az := a[2]!
    let bx := b[0]!; let by_ := b[1]!; let bz := b[2]!
    let ddx := bx - ax; let ddy := by_ - ay; let ddz := bz - az
    let dl := Float.sqrt (ddx * ddx + ddy * ddy + ddz * ddz)
    if dl > 0.25 then
      let ux := ddx / dl; let uy := ddy / dl; let uz := ddz / dl
      let proj := ax * ux + ay * uy + az * uz
      let ex := ax - proj * ux; let ey := ay - proj * uy; let ez := az - proj * uz
      let ln : Chain CGA3 3 Float := (point3 ax ay az ∧ point3 bx by_ bz) ∧ inf CGA3
      match interpreteCGA3 ln.toMultivector with
      | .line (ox, oy, oz) (dx, dy, dz) =>
        let align := (dx * ux + dy * uy + dz * uz).abs
        t := t.check (near ox ex 1e-5 && near oy ey 1e-5 && near oz ez 1e-5 && near align 1.0 1e-5)
          "interpreteCGA3 random OPNS line recovers origin & direction"
      | _ => t := t.bad "interpreteCGA3 random OPNS line wrong kind"
  -- 5. Real circles through 3 points in arbitrary planes (15 random trials)
  for _ in [0:15] do
    let c ← randPoint 3
    let cx := c[0]!; let cy := c[1]!; let cz := c[2]!
    let nL := unit (← randPoint 3)
    let nx := nL[0]!; let ny := nL[1]!; let nz := nL[2]!
    -- Build orthonormal tangent pair (u, v) ⊥ n
    let (rx, ry, rz) := if nx.abs < 0.9 then (1.0, 0.0, 0.0) else (0.0, 1.0, 0.0)
    let ux0 := ry * nz - rz * ny; let uy0 := rz * nx - rx * nz; let uz0 := rx * ny - ry * nx
    let ul := Float.sqrt (ux0 * ux0 + uy0 * uy0 + uz0 * uz0)
    let ux := ux0 / ul; let uy := uy0 / ul; let uz := uz0 / ul
    let vx := ny * uz - nz * uy; let vy := nz * ux - nx * uz; let vz := nx * uy - ny * ux
    let rk ← Tests.Gen.int 2 16
    let r := rk.toFloat / 4.0
    let p1 := point3 (cx + r * ux) (cy + r * uy) (cz + r * uz)
    let p2 := point3 (cx + r * vx) (cy + r * vy) (cz + r * vz)
    let p3 := point3 (cx - r * ux) (cy - r * uy) (cz - r * uz)
    let circ : Chain CGA3 3 Float := (p1 ∧ p2) ∧ p3
    match interpreteCGA3 circ.toMultivector with
    | .circle ctr nrm rad false =>
      let ndot := (ctr.1 - cx).abs + (ctr.2.1 - cy).abs + (ctr.2.2 - cz).abs
      let align := (nrm.1 * nx + nrm.2.1 * ny + nrm.2.2 * nz).abs
      t := t.check (ndot < 1e-5 && near align 1.0 1e-5 && near rad r 1e-5)
        "interpreteCGA3 real circle recovers center, normal, radius"
    | _ => t := t.bad "interpreteCGA3 real circle wrong kind"
  -- 6. Real & imaginary spheres and planes (IPNS & OPNS)
  let spReal := dualSphere3 1.0 (-2.0) 3.0 2.5
  match interpreteCGA3 spReal.toMultivector (isIPNS := true) with
  | .sphere (cx, cy, cz) rad false =>
    t := t.check (near cx 1.0 1e-6 && near cy (-2.0) 1e-6 && near cz 3.0 1e-6 && near rad 2.5 1e-6)
      "interpreteCGA3 IPNS real sphere"
  | _ => t := t.bad "interpreteCGA3 IPNS real sphere wrong kind"
  -- Imaginary sphere: up(c) + ½r²∞ (r² = -4)
  let spImag := point3 1.0 0.0 (-1.0) + (2.0 : Float) • inf CGA3
  match interpreteCGA3 spImag.toMultivector (isIPNS := true) with
  | .sphere (cx, cy, cz) rad true =>
    t := t.check (near cx 1.0 1e-6 && near cy 0.0 1e-6 && near cz (-1.0) 1e-6 && near rad 2.0 1e-6)
      "interpreteCGA3 IPNS imaginary sphere"
  | _ => t := t.bad "interpreteCGA3 IPNS imaginary sphere wrong kind"
  -- Plane
  let pl3 := dualPlane3 0.0 1.0 0.0 2.5
  match interpreteCGA3 pl3.toMultivector (isIPNS := true) with
  | .plane (cx, cy, cz) (nx, ny, nz) =>
    t := t.check (near cx 0.0 1e-6 && near cy 2.5 1e-6 && near cz 0.0 1e-6 &&
                  near nx 0.0 1e-6 && near ny 1.0 1e-6 && near nz 0.0 1e-6)
      "interpreteCGA3 IPNS plane"
  | _ => t := t.bad "interpreteCGA3 IPNS plane wrong kind"
  -- Imaginary circle: meet of two disjoint spheres (dual of S1 ∧ S2 in IPNS)
  let s1 := dualSphere3 (-2.0) 0.0 0.0 1.0
  let s2 := dualSphere3 2.0 0.0 0.0 1.0
  match interpreteCGA3 (s1 ∧ s2).toMultivector (isIPNS := true) with
  | .circle ctr nrm rad true =>
    t := t.check (near ctr.1 0.0 1e-5 && near ctr.2.1 0.0 1e-5 && near ctr.2.2 0.0 1e-5 &&
                  near nrm.1.abs 1.0 1e-5 && near rad (Float.sqrt 3.0) 1e-5)
      "interpreteCGA3 imaginary circle from disjoint spheres"
  | _ => t := t.bad "interpreteCGA3 imaginary circle wrong kind"
  -- 7. CGA2 circle & line
  let c2 : Chain CGA2 3 Float := (point2 1.0 0.0 ∧ point2 0.0 1.0) ∧ point2 (-1.0) 0.0
  match interpreteCGA2 c2.toMultivector with
  | .circle (cx, cy, _) _ rad false =>
    t := t.check (near cx 0.0 1e-6 && near cy 0.0 1e-6 && near rad 1.0 1e-6)
      "interpreteCGA2 unit circle"
  | _ => t := t.bad "interpreteCGA2 circle wrong kind"
  let l2 : Chain CGA2 3 Float := (point2 0.0 1.0 ∧ point2 2.0 1.0) ∧ inf CGA2
  match interpreteCGA2 l2.toMultivector with
  | .line (_, oy, _) (dx, dy, _) =>
    t := t.check (near oy 1.0 1e-6 && near dx.abs 1.0 1e-6 && near dy 0.0 1e-6)
      "interpreteCGA2 horizontal line"
  | _ => t := t.bad "interpreteCGA2 line wrong kind"
  -- 8. Fast FloatArray vecArr / coordsArr / translateChain
  let fa := (((FloatArray.emptyWithCapacity 3).push 1.25).push (-0.5)).push 2.5
  let cv : CVec CGA3 := vecArr fa
  let ca := coordsArr cv
  t := t.check (ca.size == 3 && near (ca.get! 0) 1.25 && near (ca.get! 1) (-0.5) && near (ca.get! 2) 2.5)
    "CGA3 vecArr/coordsArr FloatArray roundtrip"
  let shifted := translateChain (vec3 1.0 2.0 (-1.0)) (point3 0.5 0.5 0.5)
  match down3? shifted with
  | some (x, y, z) =>
    t := t.check (near x 1.5 1e-8 && near y 2.5 1e-8 && near z (-0.5) 1e-8)
      "CGA3 translateChain fused spinor sandwich"
  | none => t := t.bad "CGA3 translateChain none"
  return t

set_option maxHeartbeats 2000000 in
/-- Run the suite. -/
def run : IO Tally := do
  let g : Tests.Gen Tally := do
    let a ← checks S!"∞∅++" 2 "CGA2" 40
    let b ← checks S!"∞∅+++" 3 "CGA3" 40
    let c ← checks S!"∞∅++++" 4 "CGA4" 20
    let d ← checkInterprete
    return ((a.merge b).merge c).merge d
  return Tests.Gen.run 0xC0FFEE g

end GrassmannTests.ConformalSuite
