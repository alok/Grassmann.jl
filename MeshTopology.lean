import MeshTopology.Basic
import MeshTopology.Product
import MeshTopology.Quotient
import MeshTopology.Grid
import MeshTopology.Sparse
import MeshTopology.Simplex
import MeshTopology.Element
import MeshTopology.Lagrange
import MeshTopology.Resample
import MeshTopology.Proofs
import MeshTopology.Api

/-!
# MeshTopology

Lean port of Michael Reed's MeshTopology.jl 0.1.0, the combinatorial mesh layer under Cartan.jl:
integer-only topologies (node ids, element connectivity, boundary gluings) with no coordinates.
Semantics, citations and the defect list: `docs/port-notes/meshtopology.md` and
`oracle/meshtopology/defects.toml`; every constructor and query is checked against the Julia oracle
(`Tests/MeshTopology`).

## Structured grids

* `ProductTopology N` (`Product`): lazy Cartesian grids of integer axis vectors (`AxisMap`), with
  Julia's promotion, `resize?`/`resample?`/`exclude`/`cross`, `summary`/`showString`.
* `QuotientTopology N` (`Quotient`): grids of sizes `size : Vector Nat N` whose faces
  (`Fin (2*N)`) are glued (`Glue`): `openTop`, `mirror`, `clamped`, `torus`, `cylinder`, `mobius`,
  `wing`, `hopf2`/`hopf3`, `klein`, `cone`, `tube2`/`tube3`, `ball`, `sphere`, `geographic`;
  products `cross`, `crossInt`, `intCross`, `crossSphere`, `crossSector`; slices `slice`/`sliceAt?`
  and `axisTopology`; `resize?`, `resample?`; Julia's `(p, q, r)` tables via `toTable`/`ofTable?`.
* Stencil lookups: `ghost m K idx` (Julia `m[Val(K), idx…]`), `ghostLinear`, and the precomputed
  `NeighborTable` (one array read per neighbor).
* Meshes of grids (`Grid`): `elementfuns` (Julia-exact node identification),
  `elementfunsClosed` (transitive), `vertices`, `verticesInv`, `duplicates`, `linearElements`,
  `BilinearTopology`.

## Simplex meshes

* `SimplexTopology N` (`Simplex`): `N`-vertex elements stored flat with their shape in the type;
  sub-meshes (`getSub`, `byVertices`), `subImmersion`, `fullImmersion`, `complement`, `refine`;
  `valid`/`vertexFin` for bounds-check-free gathers.
* `DiscontinuousTopology N`: per-element private nodes (`discontinuous`, `disconnect`).
* Combinatorics (`Element`): `edges` (colex), `edgesIndices`, `faces`, `facets`, `facetsWith`
  (oriented boundary coefficients), `facetsIndices`, `skeleton`, `incidence`, `adjacency`,
  `neighbors`, `facetSigns`, `degrees`, `weights`, `interp`.
* Lagrange elements (`Lagrange`): `LagrangeEdges M`, `LagrangeTriangles M`,
  `LagrangeTetrahedra M` with Julia's node numbering, typed getters `getVec` returning
  `Vector Nat (lagrangeSimplex d M)`, the oriented `LagrangeTetrahedra.getConforming`, and
  `refinement`.

`Proofs` holds the kernel-checked facts: ghost resolution lands in the grid, the fast resolver
equals its reference form, `CrossRange` is an involution, the Lagrange node counts, and the
discontinuous numbering bijection.
-/
