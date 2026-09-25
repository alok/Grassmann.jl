import MeshTopology

/-!
Benchmarks of MeshTopology's hot paths (compare `oracle/meshtopology/bench.jl`): ghost lookups of
quotient grids (Cartan's stencils call them per point, per axis), the precomputed
`NeighborTable`, node identification, and the simplex combinatorics of a large triangle mesh.

`run` prints `name: time` lines (best of several repetitions) and a checksum so that nothing is
optimized away.
-/

open MeshTopology

namespace Tests.MeshTopology.Bench

/-- An opaque identity: the compiler cannot see through it, so work that depends on its result
is neither hoisted out of the timing loop nor shared between repetitions. -/
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
def fmt (ns : Nat) : String :=
  if ns < 10000 then s!"{ns} ns"
  else if ns < 10000000 then s!"{ns / 1000}.{ns / 100 % 10} µs"
  else s!"{ns / 1000000}.{ns / 100000 % 10} ms"

/-- Every one-step stencil query `(a+1, p ± e_a)` of the grid (precomputed, not timed). -/
def queries {N : Nat} (m : QuotientTopology N) : Array (Nat × Vector Int N) := Id.run do
  let mut out := #[]
  for p in [0:m.length] do
    let idx := (cartesianIndex m.size (p + 1)).map (Int.ofNat ·)
    for h : a in [0:N] do
      for d in [-1, 1] do
        out := out.push (a + 1, idx.set a (idx[a]'h.2.1 + d))
  return out

/-- Sum of the first coordinates of `m.ghost K q` over the queries. -/
@[noinline] def sweepGhost {N : Nat} (m : QuotientTopology N) (qs : Array (Nat × Vector Int N)) :
    Int :=
  qs.foldl (fun acc (K, q) => acc + (m.ghost K q)[0]!) 0

/-- The same through `ghostLinear`. -/
@[noinline] def sweepLinear {N : Nat} (m : QuotientTopology N) (qs : Array (Nat × Vector Int N)) :
    Nat :=
  qs.foldl (fun acc (K, q) => acc + m.ghostLinear K q) 0

/-- The same through a precomputed `NeighborTable`. -/
@[noinline] def sweepTable {N : Nat} (t : QuotientTopology.NeighborTable N) : Nat :=
  go 0 0
where
  /-- Tail-recursive walk over the table (every entry). -/
  go (k acc : Nat) : Nat :=
    if h : k < t.table.size then go (k + 1) (acc + t.table[k]) else acc
  termination_by t.table.size - k

/-- Structured triangulation of an `nx × ny` node grid. -/
def gridTris (nx ny : Nat) : Array (Vector Nat 3) := Id.run do
  let mut out := #[]
  for j in [0:ny - 1] do
    for i in [0:nx - 1] do
      let a := i + 1 + j * nx
      out := (out.push #v[a, a + 1, a + nx + 1]).push #v[a, a + nx + 1, a + nx]
  return out

/-- Run the benchmarks (`smoke`: tiny sizes, one repetition). -/
def run (smoke : Bool := false) : IO Unit := do
  let reps := if smoke then 1 else 7
  let n := if smoke then 9 else 61
  let report (name : String) (ns count : Nat) : IO Unit :=
    let each := ns * 10 / max count 1
    IO.println (s!"{name}: {fmt ns}" ++ (if count > 1 then s!" ({each / 10}.{each % 10} ns each)" else ""))
  let mut check : Nat := 0
  -- ghost lookups
  for (name, ⟨N, m⟩) in ([("Torus(61,61)", (⟨2, .torus #v[n, n]⟩ : Σ N, QuotientTopology N)),
      ("Sphere(61,61)", ⟨2, .sphere #v[n, n]⟩), ("Mobius(61,61)", ⟨2, .mobius #v[n, n]⟩),
      ("Hopf(7,60,61)", ⟨3, .hopf3 (if smoke then #v[4, 5, 5] else #v[7, 60, 61])⟩)] :
      List (String × Σ N, QuotientTopology N)) do
    let lookups := 2 * N * m.length
    let qs := queries m
    let (t1, r1) ← timeBest reps fun s => sweepGhost (blackBox s m) qs
    report s!"ghost sweep {name}" t1 lookups
    let (t2, r2) ← timeBest reps fun s => sweepLinear (blackBox s m) qs
    report s!"ghostLinear sweep {name}" t2 lookups
    let (t3, tbl) ← timeBest reps fun s => (blackBox s m).neighborTable
    report s!"neighborTable build {name}" t3 1
    let (t4, r4) ← timeBest reps fun s => sweepTable (blackBox s tbl)
    report s!"neighborTable sweep {name}" t4 lookups
    let (t5, efs) ← timeBest reps fun s => (blackBox s m).elementfuns
    report s!"elementfuns {name}" t5 1
    let (t6, cl) ← timeBest reps fun s => (blackBox s m).elementfunsClosed
    report s!"elementfunsClosed {name}" t6 1
    check := check + r1.toNat + r2 + r4 + efs.size + cl.size
  let (t7, b) ← timeBest reps fun s => BilinearTopology.ofQuotient (blackBox s (.sphere #v[n, n]))
  report "BilinearTopology Sphere(61,61)" t7 1
  check := check + b.nodes
  -- simplex combinatorics on a 200×200-node triangle grid
  let g := if smoke then 12 else 200
  let els := gridTris g g
  let (t8, t) ← timeBest reps fun s => SimplexTopology.ofElements (blackBox s els)
  report s!"SimplexTopology {els.size} triangles" t8 1
  let (t9, es) ← timeBest reps fun s => (blackBox s t).edges
  report "edges" t9 1
  let (t10, ei) ← timeBest reps fun s => (blackBox s t).edgesIndicesWith es
  report "edgesindices" t10 1
  let (t11, nb) ← timeBest reps fun s => (blackBox s t).neighbors
  report "neighbors" t11 1
  let (t12, inc) ← timeBest reps fun s => (blackBox s t).incidence
  report "incidence" t12 1
  let (t13, dg) ← timeBest reps fun s => (blackBox s t).degrees
  report "degrees" t13 1
  let (t14, fs) ← timeBest reps fun s => (blackBox s t).facetsWith (Array.replicate t.elements 1)
  report "facets(t, ones)" t14 1
  let (t15, L) ← timeBest reps fun s => (LagrangeTriangles.ofParts (M := 3) (blackBox s t) es ei).topology
  report "LagrangeTriangles{3} node lists" t15 1
  let L3 : LagrangeTriangles 3 := .ofParts t es ei
  let (t16, Lv) ← timeBest reps fun s =>
    let L := blackBox s L3
    (Array.range L.t.elements).map fun k => L.getVec (k + 1)
  report "LagrangeTriangles{3} typed node lists (getVec)" t16 1
  check := check + Lv.size
  check := check + es.totalElements + ei.totalElements + nb.size + inc.nnz + dg.size + fs.2.size + L.size
  IO.println s!"checksum {check}"

end Tests.MeshTopology.Bench
