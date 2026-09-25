import MeshTopology.Basic
import MeshTopology.Product
import MeshTopology.Quotient
import MeshTopology.Grid

/-!
# MeshTopology

Lean port of Michael Reed's MeshTopology.jl 0.1.0 (the combinatorial mesh layer under
Cartan.jl): integer-only topologies with no coordinates. See `docs/port-notes/meshtopology.md`.

* `ProductTopology N`: lazy Cartesian grids of integer axis vectors.
* `QuotientTopology N`: structured grids with face gluings (torus, Möbius, Klein, sphere, ball,
  cone, Hopf, …), their ghost-index resolver, slices and products.
* `elementfuns`/`vertices`, multilinear cells and `BilinearTopology`: meshes of quotient grids.
-/
