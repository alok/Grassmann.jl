import Cartan.Interp
import Cartan.Product

/-!
# Display of fields and bases

Julia prints fields through its generic `AbstractArray` display: a header with the (long) type
and one `base ↦ fiber` element per line, compact (`base↦fiber`) inside matrices
(`docs/port-notes/cartan-core.md` §5). The elements follow Julia exactly (`LocalTensor`, `Coordinate`,
`AffinePoint`, `Chain` display); the header is a simplified `dims TensorField` (Julia's alignment
padding and type strings are not reproduced, port notes §5 rule 8).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-- The array shape of a base (Julia `size(m)`). -/
class BaseShape (M : Type) where
  /-- Julia `size(m)`. -/
  shape : M → List Nat

instance {N : Nat} {P G : Type} : BaseShape (GridBundle N P G) := ⟨fun b => b.size.toList⟩
instance {n : Nat} {P G : Type} : BaseShape (SimplexBundle n P G) := ⟨fun b => [b.top.nodes]⟩
instance {n : Nat} {P G : Type} : BaseShape (FaceBundle n P G) := ⟨fun b => [b.top.elements]⟩
instance {n : Nat} {P G : Type} : BaseShape (DiscontinuousBundle n P G) := ⟨fun b => [b.top.nodes]⟩
instance {P G : Type} [FlatFiber P] : BaseShape (PointCloud P G) := ⟨fun b => [b.size]⟩
instance {M : Type} [FrameBundle M] : BaseShape (FiberProductBundle M) :=
  ⟨fun b => [card b.space, b.axis.length]⟩

/-- Julia's array-size prefix: `5-element` for vectors, `3×4` otherwise. -/
def dimsString : List Nat → String
  | [n] => s!"{n}-element"
  | ds => "×".intercalate (ds.map toString)

namespace GridBundle

variable {N : Nat} {P G : Type}

/-- A summary of a grid bundle: its shape, gluing and points. -/
def summary (b : GridBundle N P G) : String :=
  s!"{dimsString b.size.toList} GridBundle over {b.space} with {b.top.summary}"

instance : ToString (GridBundle N P G) := ⟨summary⟩

end GridBundle

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {P G F : Type} [FlatFiber F] [Coordinates M P G]
  [ShowFiber (Coordinate P G)] [ShowFiber F]

/-- Julia `show(io, MIME"text/plain", t)` (simplified header): the shape, then one element per
line in column-major order (compact for arrays of dimension ≥ 2, as Julia prints matrices). -/
def showString [BaseShape M] (t : TensorField m F) : String :=
  let ds := BaseShape.shape m
  let compact := ds.length ≥ 2
  let lines := (List.range (card m)).map fun i => " " ++ showFiber compact (t.localAt i)
  "\n".intercalate (s!"{dimsString ds} TensorField:" :: lines)

instance [BaseShape M] : ToString (TensorField m F) := ⟨showString⟩

/-- Julia `repr(t)` (2-argument `show`): the elements as a bracketed list, `[a ↦ b, …]`. -/
def reprString (t : TensorField m F) : String :=
  "[" ++ ", ".intercalate ((List.range (card m)).map fun i => showFiber false (t.localAt i)) ++ "]"

end TensorField

end Cartan
