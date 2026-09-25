import Cartan.ProductSpace

/-!
# Local fibers: `Coordinate` and `LocalTensor`

Julia's `LocalFiber{B,F} <: Number` (Cartan.jl `src/topology.jl:278-517`) is a `base ↦ fiber` pair:

* `Coordinate{P,G}`: a point `P` with its metric `G` (the elements of a base, `FrameBundle`);
* `LocalTensor{B,F}` (alias `Section`, operator `↦`): a base value with a fiber value (the
  elements of a `TensorField`);
* `LocalPrincipal{M,G}`: a principal-bundle pair.

Arithmetic on a local fiber acts on its fiber and keeps the base of the left operand (Julia
`topology.jl:466-514`). For a `Coordinate` the fiber is the *metric*: Julia's `2 * Coordinate(p)`
tries `2 * InducedMetric()` and throws (port notes §2.7), so no arithmetic is defined on
`Coordinate` here; functions of points read `point`.

Display follows `topology.jl:316-333`: a coordinate with the induced metric prints as its point,
anything else as `base ↦ fiber` (`base↦fiber` in compact context).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-- Julia `Coordinate{P,G}` (`topology.jl:351-355`): a point with its metric (`Induced` for the
fiber algebra's own). -/
structure Coordinate (P : Type) (G : Type := Induced) where
  /-- Julia `point(c)` = `base(c)`. -/
  point : P
  /-- Julia `metricextensor(c)` = `fiber(c)`. -/
  metric : G
  deriving BEq, Inhabited

/-- Julia `Coordinate(p)` with the induced metric. -/
@[inline] def Coordinate.induced {P : Type} (p : P) : Coordinate P := ⟨p, {}⟩

/-- Julia `LocalTensor{B,F}` = `Section` (`topology.jl:424-433`): the value `fiber` of a field at
the base element `base`. -/
structure LocalTensor (B F : Type) where
  /-- Julia `base(s)` (`s[]`). -/
  base : B
  /-- Julia `fiber(s)`. -/
  fiber : F
  deriving BEq, Inhabited

/-- Julia `Section = LocalTensor` (`topology.jl:433`). -/
abbrev Section := LocalTensor

/-- Julia `LocalPrincipal{M,G}` (`topology.jl:404-408`): a principal base value and group value. -/
structure LocalPrincipal (M G : Type) where
  /-- Julia `principalbase(s)`. -/
  base : M
  /-- Julia `principalfiber(s)`. -/
  fiber : G
  deriving BEq, Inhabited

/-- Julia `b ↦ f` = `LocalTensor(b, f)` (`topology.jl:434`); right-associative, so
`p ↦ g ↦ f` is `LocalTensor(p, LocalTensor(g, f))`. Scoped: `open Cartan`. -/
scoped infixr:25 " ↦ " => LocalTensor.mk

namespace LocalTensor

variable {B F F' F'' : Type}

/-- Julia `basepoint(s) = point(base(s))` (`topology.jl:301`). -/
@[inline] def basepoint {P G : Type} (s : LocalTensor (Coordinate P G) F) : P := s.base.point

/-- Julia `localfiber(s)` (`topology.jl:437-438`). -/
@[inline] def localfiber (s : LocalTensor B F) : F := s.fiber

/-- Apply a function to the fiber, keeping the base (Julia `(m::TensorNested)(x::LocalTensor)`,
`topology.jl:440`, and the unary lifts of `topology.jl:470-478`). -/
@[inline] def map (f : F → F') (s : LocalTensor B F) : LocalTensor B F' := ⟨s.base, f s.fiber⟩

/-- Combine two local tensors fiberwise; the base of the first is kept and the second's is
ignored (Julia `topology.jl:479-494`, no base check). -/
@[inline] def zipWith (f : F → F' → F'') (a : LocalTensor B F) (b : LocalTensor B F') :
    LocalTensor B F'' := ⟨a.base, f a.fiber b.fiber⟩

/-- Julia `type(b, f::Function) = type(b, f(b))` (`topology.jl:496`): `LocalTensor(2.0, x->x^2)`
is `2.0 ↦ 4.0`. -/
@[inline] def ofFn (b : B) (f : B → F) : LocalTensor B F := ⟨b, f b⟩

instance [HAdd F F' F''] : HAdd (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith (· + ·)⟩
instance [HSub F F' F''] : HSub (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith (· - ·)⟩
instance [HMul F F' F''] : HMul (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith (· * ·)⟩
instance [HDiv F F' F''] : HDiv (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith (· / ·)⟩
instance [Neg F] : Neg (LocalTensor B F) := ⟨map (- ·)⟩
instance [HMul Float F F'] : HMul Float (LocalTensor B F) (LocalTensor B F') := ⟨fun x s => s.map (x * ·)⟩
instance [HMul F Float F'] : HMul (LocalTensor B F) Float (LocalTensor B F') := ⟨fun s x => s.map (· * x)⟩
instance [HDiv F Float F'] : HDiv (LocalTensor B F) Float (LocalTensor B F') := ⟨fun s x => s.map (· / x)⟩

instance [Wedge F F' F''] : Wedge (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith wedge⟩
instance [Vee F F' F''] : Vee (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith vee⟩
instance [Contraction F F' F''] :
    Contraction (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') := ⟨zipWith contraction⟩
instance [WedgeDot F F' F''] : WedgeDot (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith wedgedot⟩
instance [Sandwich F F' F''] : Sandwich (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith sandwich⟩
/-- Julia `a × b = ⋆(a ∧ b)` for local tensors: the intended result of `topology.jl:449`, which
calls `TensorField(::Float64, …)` and throws (B11). -/
instance [Cross F F' F''] : Cross (LocalTensor B F) (LocalTensor B F') (LocalTensor B F'') :=
  ⟨zipWith cross⟩
instance [Hodge F F'] : Hodge (LocalTensor B F) (LocalTensor B F') := ⟨map hodge⟩
instance [Reverse F] : Reverse (LocalTensor B F) := ⟨map Reverse.reverse⟩
instance [Involute F] : Involute (LocalTensor B F) := ⟨map involute⟩
instance [Clifford F] : Clifford (LocalTensor B F) := ⟨map clifford⟩

/-- Julia `a < b` on local tensors = `contraction(b, a)` (`topology.jl:443, 459-461`): a Grassmann
contraction, not an order (`(1.0 ↦ 2.0) < (1.0 ↦ 3.0)` is `1.0 ↦ 6.0`). -/
@[inline] def lt [Contraction F' F F''] (a : LocalTensor B F) (b : LocalTensor B F') :
    LocalTensor B F'' := ⟨a.base, contraction b.fiber a.fiber⟩

end LocalTensor

/-! ## Display -/

/-- Julia `show` of a pair `b ↦ f` (`topology.jl:316-333`, tightly typed pairs). -/
def showPair {B F : Type} [ShowFiber B] [ShowFiber F] (compact : Bool) (b : B) (f : F) : String :=
  showFiber compact b ++ (if compact then "↦" else " ↦ ") ++ showFiber compact f

/-- A coordinate with the induced metric prints as its point (`topology.jl:317`). -/
instance (priority := high) {P : Type} [ShowFiber P] : ShowFiber (Coordinate P Induced) :=
  ⟨fun c x => showFiber c x.point⟩

/-- A coordinate with a stored metric prints `point ↦ metric`. -/
instance {P G : Type} [ShowFiber P] [ShowFiber G] : ShowFiber (Coordinate P G) :=
  ⟨fun c x => showPair c x.point x.metric⟩

instance {B F : Type} [ShowFiber B] [ShowFiber F] : ShowFiber (LocalTensor B F) :=
  ⟨fun c x => showPair c x.base x.fiber⟩

instance {M G : Type} [ShowFiber M] [ShowFiber G] : ShowFiber (LocalPrincipal M G) :=
  ⟨fun c x => showPair c x.base x.fiber⟩

instance {P G : Type} [ShowFiber (Coordinate P G)] : ToString (Coordinate P G) := ⟨showFiber false⟩
instance {B F : Type} [ShowFiber (LocalTensor B F)] : ToString (LocalTensor B F) := ⟨showFiber false⟩

end Cartan
