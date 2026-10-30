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

set_option maxHeartbeats 2000000 in
/-- Run the suite. -/
def run : IO Tally := do
  let g : Tests.Gen Tally := do
    let a ← checks S!"∞∅++" 2 "CGA2" 40
    let b ← checks S!"∞∅+++" 3 "CGA3" 40
    let c ← checks S!"∞∅++++" 4 "CGA4" 20
    return (a.merge b).merge c
  return Tests.Gen.run 0xC0FFEE g

end GrassmannTests.ConformalSuite
