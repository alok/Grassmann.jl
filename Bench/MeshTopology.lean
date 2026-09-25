import Bench.Harness
import MeshTopology

/-!
# `meshtopology`: quotient-grid stencils and simplex combinatorics

Julia twin: `oracle/bench/meshtopology.jl` (the `Fixed` module of
`oracle/meshtopology/load.jl`, same code paths as upstream for everything timed here).

* `ghost_*`: every one-step stencil query `m[Val(a), i ± e_a]` of a quotient grid (Cartan's
  stencils call these per point and axis), ns per lookup; `ghostLinear_*` and
  `neighbortable_*` are the Lean-only alternatives (linear index, precomputed table).
* `elementfuns_*`, `bilinear_sphere`: per-topology setup.
* `simplex_topology` … `lagrange3_nodes`: the simplex combinatorics of a 200×200-node
  triangulation (79 202 triangles). Julia's `vertices`/`findfirst` make several of these
  quadratic.
-/

namespace Bench.MeshTopology

open _root_.MeshTopology Bench

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
def sweepGhost {N : Nat} (m : QuotientTopology N) (qs : Array (Nat × Vector Int N)) : Int :=
  qs.foldl (fun acc (K, q) => acc + (m.ghost K q)[0]!) 0

/-- The same through `ghostLinear`. -/
def sweepLinear {N : Nat} (m : QuotientTopology N) (qs : Array (Nat × Vector Int N)) : Nat :=
  qs.foldl (fun acc (K, q) => acc + m.ghostLinear K q) 0

/-- The same through a precomputed `NeighborTable`. -/
def sweepTable {N : Nat} (t : QuotientTopology.NeighborTable N) : Nat :=
  go 0 0
where
  /-- Tail-recursive walk over the table (every entry). -/
  go (k acc : Nat) : Nat :=
    if h : k < t.table.size then go (k + 1) (acc + t.table[k]) else acc
  termination_by t.table.size - k

/-- Structured triangulation of an `nx × ny` node grid (as Julia's `gridtris`). -/
def gridTris (nx ny : Nat) : Array (Vector Nat 3) := Id.run do
  let mut out := #[]
  for j in [0:ny - 1] do
    for i in [0:nx - 1] do
      let a := i + 1 + j * nx
      out := (out.push #v[a, a + 1, a + nx + 1]).push #v[a, a + nx + 1, a + nx]
  return out

/-- Benchmarks of one quotient topology. -/
def topologyCases {N : Nat} (tag : String) (dims : String) (m : QuotientTopology N) : BenchM Unit := do
  let lookups := 2 * N * m.length
  let qs := queries m
  bench s!"ghost_{tag}" (ops := lookups) (param := dims) fun s => sweepGhost (blackBox s m) qs
  bench s!"ghostLinear_{tag}" (ops := lookups) (param := dims) fun s => sweepLinear (blackBox s m) qs
  bench s!"neighbortable_build_{tag}" (param := dims) fun s => (blackBox s m).neighborTable.table.size
  let tbl := m.neighborTable
  bench s!"neighbortable_sweep_{tag}" (ops := lookups) (param := dims) fun s => sweepTable (blackBox s tbl)
  bench s!"elementfuns_{tag}" (param := dims) fun s => (blackBox s m).elementfuns
  bench s!"elementfunsClosed_{tag}" (param := dims) fun s => (blackBox s m).elementfunsClosed

/-- The suite. -/
def suite : Suite := ⟨"meshtopology", do
  let n ← size 61 9
  let d2 := s!"{n}×{n}"
  topologyCases "torus" d2 (.torus #v[n, n])
  topologyCases "sphere" d2 (.sphere #v[n, n])
  topologyCases "mobius" d2 (.mobius #v[n, n])
  let hopf := if (← smoke) then #v[4, 5, 5] else #v[7, 60, 61]
  topologyCases "hopf" s!"{hopf[0]}×{hopf[1]}×{hopf[2]}" (.hopf3 hopf)
  let sph : QuotientTopology 2 := .sphere #v[n, n]
  bench "bilinear_sphere" (param := d2) fun s => (BilinearTopology.ofQuotient (blackBox s sph)).nodes
  -- simplex combinatorics on a g×g-node triangle grid
  let g ← size 200 12
  let els := gridTris g g
  let p := s!"{els.size} triangles"
  bench "simplex_topology" (param := p) fun s => (SimplexTopology.ofElements (blackBox s els)).elements
  let t := SimplexTopology.ofElements els
  let es := t.edges
  let ei := t.edgesIndicesWith es
  bench "edges" (param := p) fun s => (blackBox s t).edges.totalElements
  bench "edgesindices" (param := p) fun s => ((blackBox s t).edgesIndicesWith es).totalElements
  bench "neighbors" (param := p) fun s => (blackBox s t).neighbors.size
  bench "incidence" (param := p) fun s => (blackBox s t).incidence.nnz
  bench "degrees" (param := p) fun s => (blackBox s t).degrees.size
  bench "facets_ones" (param := p) fun s => ((blackBox s t).facetsWith (Array.replicate t.elements 1)).2.size
  -- Julia's twin includes `edgesindices` (its constructor recomputes it)
  bench "lagrange3_nodes" (param := p) fun s =>
    let t := blackBox s t
    (LagrangeTriangles.ofParts (M := 3) t es (t.edgesIndicesWith es)).topology.size
  let L3 : LagrangeTriangles 3 := .ofParts t es ei
  bench "lagrange3_getvec" (param := p) fun s =>
    let L := blackBox s L3
    ((Array.range L.t.elements).map fun k => L.getVec (k + 1)).size⟩

end Bench.MeshTopology
