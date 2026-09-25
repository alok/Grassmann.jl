import FlowGeometry

/-!
Benchmarks of FlowGeometry's constructors (compare `oracle/flowgeometry/bench.jl`): parsing a
NACA designation, sampling the profile families at 150 points, the airfoil surfaces and closed
outline of `NACA"2412"`, the Joukowski curve, the default Rakich C-mesh (`initrakich()`, 5 151
points), the wing surface of `NACA"6511"` (150 × 299), a 25-point convex hull, two levels of
sphere subdivision, and single-point profile evaluation.

`run` prints `name: time per call` (best of several repetitions) and a checksum so that nothing
is optimized away. Inputs pass through `blackBox`, so no work is hoisted out of the timing loops.
-/

open FlowGeometry Cartan Grassmann DirectSum JuliaBase

namespace Tests.FlowGeometry.Bench

/-- An opaque identity: work that depends on its result is neither hoisted out of the timing loop
nor shared between repetitions. -/
@[noinline] def blackBox {α : Type} (_salt : Nat) (x : α) : α := x

/-- Best wall time (ns) of `reps` runs of `f` (each run gets a different salt), and the last
result. -/
def timeBest {α : Type} (reps : Nat) (f : Nat → α) : IO (Nat × α) := do
  let mut best := 0
  let mut out := f reps
  for k in [0:reps] do
    let t0 ← IO.monoNanosNow
    out := f k
    let t1 ← IO.monoNanosNow
    if k == 0 || t1 - t0 < best then best := t1 - t0
  return (best, out)

/-- Format nanoseconds (one decimal). -/
def fmt (ns : Float) : String :=
  let r (x : Float) : String := toString ((x * 10).round / 10)
  if ns < 10000 then s!"{r ns} ns" else if ns < 1e7 then s!"{r (ns / 1000)} µs" else s!"{r (ns / 1e6)} ms"

/-- Repeat `f` `n` times (salted), summing a float from each result. -/
@[specialize] def repeatSum (n salt : Nat) (f : Nat → Float) : Float :=
  go n 0
where
  /-- the loop -/
  go : Nat → Float → Float
    | 0, acc => acc
    | k + 1, acc => go k (acc + f (salt * 1000003 + k))

/-- A float read of a flat array (the last element), as a checksum. -/
@[inline] def lastOf (a : FloatArray) : Float := a.get! (a.size - 1)

/-- `NACA.parse?` of a designation. -/
@[noinline] def benchParse (s : String) (salt : Nat) : Float :=
  match NACA.parse? (blackBox salt s) with
  | .ok a => natF a.samples
  | .error _ => 0

/-- The sampled field `profile(p)`. -/
@[noinline] def benchField (p : Profile) (salt : Nat) : Float := lastOf (blackBox salt p).field.data

/-- The sampled slope field. -/
@[noinline] def benchSlope (p : Profile) (salt : Nat) : Float := lastOf (blackBox salt p).slopeField.data

/-- `upper(N)`. -/
@[noinline] def benchUpper (a : Airfoil) (salt : Nat) : Float := (blackBox salt a).upper.data.get! 3

/-- `complex(N)`. -/
@[noinline] def benchComplex (a : Airfoil) (salt : Nat) : Float := (blackBox salt a).complex.data.get! 3

/-- `points(N)`. -/
@[noinline] def benchPoints (a : Airfoil) (salt : Nat) : Float := (blackBox salt a).points.points.get! 4

/-- `complex(::Joukowski)`. -/
@[noinline] def benchJoukowski (j : Joukowski) (salt : Nat) : Float := (blackBox salt j).complex.data.get! 3

/-- `initrakich(P, D, n, JL)`. -/
@[noinline] def benchRakich (T : Num) (salt : Nat) : Float :=
  let (pt, pe) := initrakich (blackBox salt T)
  lastOf pt.cloud.points + natF pe.top.elements

/-- `wing(N)`. -/
@[noinline] def benchWing (a : Airfoil) (salt : Nat) : Float := lastOf (wing (blackBox salt a)).data

/-- `convhull(p)`. -/
@[noinline] def benchHull (p : PointCloud (Chain ℝ3 1 Float)) (salt : Nat) : Float :=
  natF (convhull (blackBox salt p)).elements

/-- Two levels of sphere subdivision of the icosahedron. -/
@[noinline] def benchSphere (fac : SimplexBundle 3 (Chain ℝ4 1 Float)) (salt : Nat) : Float :=
  let s := sphereRefine (sphereRefine (blackBox salt fac))
  lastOf s.cloud.points

/-- Evaluate `e` at `n` points of `[0, 1)` (ns per evaluation). -/
@[noinline] def benchEval (e : Eval) (n salt : Nat) : Float :=
  let e := blackBox salt e
  let step := 1 / natF n
  go e step n 0 0
where
  /-- the loop -/
  go (e : Eval) (step : Float) : Nat → Float → Float → Float
    | 0, _, acc => acc
    | k + 1, x, acc => go e step k (x + step) (acc + e.value x)

/-- The icosahedron's faces (the convex hull of its vertices, outward). -/
def icoFaces : Array (Vector Nat 3) :=
  #[#v[1, 2, 3], #v[1, 7, 2], #v[1, 3, 9], #v[1, 5, 7], #v[1, 9, 5], #v[2, 8, 3], #v[2, 7, 6],
    #v[2, 6, 8], #v[3, 8, 4], #v[3, 4, 9], #v[4, 8, 10], #v[4, 11, 9], #v[4, 10, 11], #v[5, 12, 7],
    #v[5, 9, 11], #v[5, 11, 12], #v[6, 7, 12], #v[6, 10, 8], #v[6, 12, 10], #v[10, 12, 11]]

/-- 25 pseudo-random points in the plane (a fixed LCG). -/
def hullPoints : PointCloud (Chain ℝ3 1 Float) :=
  let rnd (k : Nat) : Float := natF ((k * 2654435761 + 12345) % 1000003) / 1000003 - 0.5
  .ofArray ((Array.range 25).map fun k => pt3 (rnd (2 * k)) (rnd (2 * k + 1)))

/-- Run the benchmarks (`smoke`: one repetition, few iterations). -/
def run (smoke : Bool := false) : IO Unit := do
  let reps := if smoke then 1 else 7
  let it (n : Nat) : Nat := if smoke then 1 else n
  let mut check : Float := 0
  let report (name : String) (ns : Nat) (count : Nat) : IO Unit :=
    IO.println s!"  {name}: {fmt (ns.toFloat / count.toFloat)}"
  -- parsing
  let n := it 10000
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchParse "2412")
  report "NACA\"2412\" parse" t n; check := check + c
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchParse "24012-34")
  report "NACA\"24012-34\" parse" t n; check := check + c
  -- profile fields at 150 points
  let n := it 2000
  for (name, p) in [("ClarkY{12,150}", Profile.clarkYDefault 12 150),
      ("Thickness{12,4,150}", Profile.thicknessX 12 4 150), ("Modified{12,64,150}", Profile.modifiedM 12 64 150),
      ("NACA4{24,150}", Profile.naca4 24 150), ("NACA5{230,150}", Profile.naca5 230 150),
      ("NACA6{2,150}", Profile.naca6Default 2 150), ("CircularArc{6,150}", Profile.circularArc 6 150)] do
    let (t, c) ← timeBest reps fun s => repeatSum n s (benchField p)
    report s!"profile({name})" t n; check := check + c
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchSlope (Profile.clarkYDefault 12 150))
  report "profileslope(ClarkY{12,150})" t n; check := check + c
  -- airfoils
  let a := NACA.parse! "2412"
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchUpper a)
  report "upper(NACA\"2412\")" t n; check := check + c
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchComplex a)
  report "complex(NACA\"2412\")" t n; check := check + c
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchPoints a)
  report "points(NACA\"2412\")" t n; check := check + c
  let a5 := NACA.parse! "23012"
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchComplex a5)
  report "complex(NACA\"23012\") (British)" t n; check := check + c
  let a64 := NACA.parse! "0012-64"
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchComplex a64)
  report "complex(NACA\"0012-64\")" t n; check := check + c
  let j : Joukowski := ⟨1.1, 0.1, 0.1, 1.0, 75⟩
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchJoukowski j)
  report "complex(Joukowski{1.1,0.1,0.1,1.0,75})" t n; check := check + c
  -- meshes
  let n := it 20
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchRakich 6)
  report "initrakich() (101×51)" t n; check := check + c
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchWing (NACA.parse! "6511"))
  report "wing(NACA\"6511\") (150×299)" t n; check := check + c
  let n := it 200
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchHull hullPoints)
  report "convhull (25 points)" t n; check := check + c
  let ico : SimplexBundle 3 (Chain ℝ4 1 Float) :=
    ⟨.ofArray (FlowGeometry.sphere 1), MeshTopology.SimplexTopology.ofElements icoFaces (p := some 12)⟩
  let (t, c) ← timeBest reps fun s => repeatSum n s (benchSphere ico)
  report "sphere subdivision ×2 (20 → 320 faces)" t n; check := check + c
  -- single-point evaluation
  let n := it 1000000
  for (name, p) in [("ClarkY{12}", Profile.clarkYDefault 12 150), ("Modified{12,64}", Profile.modifiedM 12 64 150),
      ("NACA6{2}", Profile.naca6Default 2 150)] do
    let e := p.eval
    let (t, c) ← timeBest reps fun s => benchEval e n s
    report s!"{name}(x) per point" t n; check := check + c
  IO.println s!"  (checksum {check})"

end Tests.FlowGeometry.Bench
