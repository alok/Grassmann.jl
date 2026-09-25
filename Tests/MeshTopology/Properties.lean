import Tests.MeshTopology.Util
import Tests.Util.Random

/-!
Randomized property tests of MeshTopology (SplitMix64, fixed seeds): invariants that hold for
every input, beyond the oracle's cases.

* Ghost resolution stays in the grid for one-layer ghosts of glued faces; `ghostLinear` and the
  `NeighborTable` agree; torus lookups are involutions.
* `elementfunsClosed` is idempotent and `vertices` numbers `1..nodes` onto the representatives.
* `edges` are strictly colex-sorted, `edgesIndices` points back to each element's own vertex
  pairs, `neighbors` is symmetric and `DiscontinuousTopology.get` is a bijection onto
  `1..N·elements`.
* Lagrange node lists stay within `1..totalNodes` and use every node of a full mesh.
-/

open Lean MeshTopology Tests.Small Tests

namespace Tests.MeshTopology.Properties

/-- A random named topology of dimension 1-3 with sizes in `3..9`. -/
def randomTopology (g : Rng) : SomeQuotient × Rng :=
  let (N, g) := g.nat 3
  let N := N + 1
  let (sizes, g) := (List.range N).foldl (fun (acc : Array Nat × Rng) _ =>
    let (k, g) := acc.2.nat 7
    (acc.1.push (k + 3), g)) (#[], g)
  let fams := match N with
    | 1 => #["Open", "Mirror", "Clamped", "Torus", "Sphere"]
    | 2 => #["Open", "Cylinder", "Mobius", "Wing", "Mirror", "Clamped", "Torus", "Hopf", "Klein",
             "Cone", "Tube", "Ball", "Sphere", "Geographic"]
    | _ => #["Open", "Mirror", "Clamped", "Torus", "Hopf", "Tube", "Ball", "Sphere"]
  let (f, g) := g.nat fams.size
  let fam := fams[f]!
  let v (k : Nat) : Vector Nat k := Vector.ofFn fun i => sizes[i.1]!
  let q : SomeQuotient := match N, fam with
    | 1, "Open" => ⟨1, .openTop (v 1)⟩ | 1, "Mirror" => ⟨1, .mirror (v 1)⟩
    | 1, "Clamped" => ⟨1, .clamped (v 1)⟩ | 1, "Torus" => ⟨1, .torus (v 1)⟩
    | 1, _ => ⟨1, .sphere (v 1)⟩
    | 2, "Open" => ⟨2, .openTop (v 2)⟩ | 2, "Cylinder" => ⟨2, .cylinder (v 2)⟩
    | 2, "Mobius" => ⟨2, .mobius (v 2)⟩ | 2, "Wing" => ⟨2, .wing (v 2)⟩
    | 2, "Mirror" => ⟨2, .mirror (v 2)⟩ | 2, "Clamped" => ⟨2, .clamped (v 2)⟩
    | 2, "Torus" => ⟨2, .torus (v 2)⟩ | 2, "Hopf" => ⟨2, .hopf2 (v 2)⟩
    | 2, "Klein" => ⟨2, .klein (v 2)⟩ | 2, "Cone" => ⟨2, .cone (v 2)⟩
    | 2, "Tube" => ⟨2, .tube2 (v 2)⟩ | 2, "Ball" => ⟨2, .ball (v 2)⟩
    | 2, "Sphere" => ⟨2, .sphere (v 2)⟩ | 2, _ => ⟨2, .geographic (v 2)⟩
    | _, "Open" => ⟨3, .openTop (v 3)⟩ | _, "Mirror" => ⟨3, .mirror (v 3)⟩
    | _, "Clamped" => ⟨3, .clamped (v 3)⟩ | _, "Torus" => ⟨3, .torus (v 3)⟩
    | _, "Hopf" => ⟨3, .hopf3 (v 3)⟩ | _, "Tube" => ⟨3, .tube3 (v 3)⟩
    | _, "Ball" => ⟨3, .ball (v 3)⟩ | _, _ => ⟨3, .sphere (v 3)⟩
  (q, g)

/-- Ghost resolution and the neighbor table. -/
def quotientProps : TestM Unit := do
  let mut g := Rng.ofSeed 0x3E54
  for _ in [0:120] do
    let (⟨N, m⟩, g') := randomTopology g
    g := g'
    let lbl := m.summary
    let tbl := m.neighborTable
    let len := m.length
    let mut inRange := true
    let mut agree := true
    for p in [0:len] do
      let idx := (cartesianIndex m.size (p + 1)).map (Int.ofNat ·)
      for h : a in [0:N] do
        for up in [false, true] do
          let step : Int := if up then 1 else -1
          let q := idx.set a (idx[a]'h.2.1 + step)
          let r := m.ghost (a + 1) q
          -- one-layer ghosts beyond a glued face land in the grid
          let i := q[a]'h.2.1
          let n := m.size[a]'h.2.1
          let face : Option (Fin (2 * N)) :=
            if i < 1 then some (QuotientTopology.lowFace ⟨a, h.2.1⟩)
            else if i > n then some (QuotientTopology.highFace ⟨a, h.2.1⟩) else none
          if let some f := face then
            if (m.glue[f]).isSome then
              inRange := inRange && (List.finRange N).all fun k => 0 < r[k] && r[k] ≤ (m.size[k] : Int)
          if hp : p < tbl.len then
            agree := agree && tbl.get ⟨a, h.2.1⟩ ⟨p, hp⟩ up == m.ghostLinear (a + 1) q
    check s!"{lbl} ghosts of glued faces stay in the grid" inRange
    check s!"{lbl} NeighborTable agrees with ghostLinear" agree
    -- closed identification: idempotent, and vertices number 1..nodes onto representatives
    let cl := m.elementfunsClosed
    check s!"{lbl} elementfunsClosed idempotent" (cl.all fun r => cl[r - 1]! == r)
    let vs := QuotientTopology.verticesOfFuns cl
    let nodes := (QuotientTopology.uniqueOrdered cl).size
    check s!"{lbl} vertices onto 1..nodes"
      (vs.all (fun v => 1 ≤ v && v ≤ nodes) && (List.range nodes).all fun k => vs.contains (k + 1))
  -- torus lookups swap the two representatives of a periodic seam: an involution under K = 0
  for (a, b) in [(3, 4), (5, 7), (8, 3)] do
    let m : QuotientTopology 2 := .torus #v[a, b]
    let ok := (List.range (a + 2)).all fun i => (List.range (b + 2)).all fun j =>
      let x : Vector Int 2 := #v[(i : Int), (j : Int)]
      let y := m.get x
      (0 < x[0] && x[0] ≤ a && 0 < x[1] && x[1] ≤ b) → m.get y == x
    check s!"Torus({a},{b}) seam swap is an involution" ok

/-- A random triangulated grid with relabelled vertices and rotated/reflected elements. -/
def randomMesh (g : Rng) : Array (Vector Nat 3) × Rng := Id.run do
  let (nx, g) := g.nat 5
  let (ny, g) := g.nat 5
  let (nx, ny) := (nx + 3, ny + 3)
  let n := nx * ny
  -- Fisher-Yates permutation
  let mut perm := (Array.range n).map (· + 1)
  let mut g := g
  for k in [0:n] do
    let (r, g') := g.nat (n - k)
    g := g'
    perm := perm.swapIfInBounds k (k + r)
  let mut out : Array (Vector Nat 3) := #[]
  for j in [0:ny - 1] do
    for i in [0:nx - 1] do
      let a := i + j * nx
      let (b, c, d) := (a + 1, a + nx, a + nx + 1)
      for tri in [#[a, b, d], #[a, d, c]] do
        let (rot, g') := g.nat 3
        let (refl, g'') := g'.nat 2
        g := g''
        let t := tri.map (perm[·]!)
        let t := (Array.range 3).map fun k => t[(k + rot) % 3]!
        let t := if refl == 1 then t.reverse else t
        out := out.push #v[t[0]!, t[1]!, t[2]!]
  return (out, g)

/-- Simplex and Lagrange invariants on random triangle meshes. -/
def simplexProps : TestM Unit := do
  let mut g := Rng.ofSeed 0x5EED
  for trial in [0:25] do
    let (els, g') := randomMesh g
    g := g'
    let t : SimplexTopology 3 := .ofElements els
    let lbl := s!"random mesh {trial}"
    let es := t.edgeList
    check s!"{lbl} edges strictly colex"
      ((List.range (es.size - 1)).all fun k =>
        let (x, y) := (es[k]!, es[k + 1]!)
        x[0] < x[1] && (x[1] < y[1] || (x[1] == y[1] && x[0] < y[0])))
    let ei := t.edgesIndices
    check s!"{lbl} edgesindices point at the element's opposite edges"
      ((Array.range t.elements).all fun k =>
        let v := t.get (k + 1)
        let ids := ei.get (k + 1)
        let pairs := #[(v[1], v[2]), (v[0], v[2]), (v[0], v[1])]
        (Array.range 3).all fun j =>
          let e := es[ids[j]! - 1]!
          let (a, b) := pairs[j]!
          e[0] == min a b && e[1] == max a b)
    let nb := t.neighbors
    check s!"{lbl} neighbors symmetric"
      ((Array.range nb.size).all fun k => nb[k]!.toList.all fun l => l == 0 || nb[l - 1]!.toList.contains (k + 1))
    let d := t.discontinuous
    let ids := d.topology.flatMap (·.toArray)
    check s!"{lbl} discontinuous nodes are a bijection"
      (ids.qsort (· < ·) == (Array.range d.totalNodes).map (· + 1))
    for M in [1, 2, 3, 4] do
      let L : LagrangeTriangles M := .ofCorners t
      let all := L.topology.flatMap id
      let used := all.foldl (fun (acc : Array Bool) v => acc.set! v true) (Array.replicate (L.totalNodes + 1) false)
      check s!"{lbl} P{M} node ids within 1..totalnodes" (all.all fun v => 1 ≤ v && v ≤ L.totalNodes)
      check s!"{lbl} P{M} every node used" ((List.range L.totalNodes).all fun v => used[v + 1]!)
      check s!"{lbl} P{M} element size" (L.topology.all (·.size == lagrangeSimplex 3 M))

/-- Run all property tests. -/
def run : TestM Unit := do
  quotientProps
  simplexProps

end Tests.MeshTopology.Properties
