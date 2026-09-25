import Cartan.Element
import Cartan.Operator

/-!
# Field kinds: Julia's `TensorField` type aliases

Cartan.jl names fields by their fiber and base (`src/Cartan.jl:118-148`): `ScalarField`,
`VectorField`, `PlaneCurve`, `SurfaceGrid`, `SimplexMap`, … are `TensorField{B,F,N,P,A}` with a
constraint on the fiber type `F` or the base `P`. Here they are abbreviations of `TensorField`
over the matching base and fiber; Julia's value constraints that types cannot carry (a
`PlaneCurve`'s chains have two components) are stated in the docstrings.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors

section Fibers

variable {M : Type} [FrameBundle M]

/-- Julia `ScalarField` (`Cartan.jl:145`): a field of reals. -/
abbrev ScalarField (m : M) := TensorField m Float

/-- Julia `GradedField{G}` (`Cartan.jl:144`): a field of grade-`G` chains of `V`. -/
abbrev GradedField (m : M) (V : TensorBundle) (G : Nat) := TensorField m (Chain V G Float)

/-- Julia `VectorField = GradedField{1}` (`Cartan.jl:146`). -/
abbrev VectorField (m : M) (V : TensorBundle) := GradedField m V 1

/-- Julia `BivectorField = GradedField{2}` (`Cartan.jl:147`). -/
abbrev BivectorField (m : M) (V : TensorBundle) := GradedField m V 2

/-- Julia `TrivectorField = GradedField{3}` (`Cartan.jl:148`). -/
abbrev TrivectorField (m : M) (V : TensorBundle) := GradedField m V 3

/-- Julia `CliffordField` (`Cartan.jl:139`): a field of multivectors. -/
abbrev CliffordField (m : M) (V : TensorBundle) := TensorField m (Multivector V Float)

/-- Julia `SpinorField` (`Cartan.jl:143`): a field of even multivectors. -/
abbrev SpinorField (m : M) (V : TensorBundle) := TensorField m (Spinor V Float)

/-- Julia `QuaternionField` (`Cartan.jl:140`): a field of quaternions, the spinors of `ℝ3`. -/
abbrev QuaternionField (m : M) := TensorField m (Spinor ℝ3 Float)

/-- Julia `ComplexMap` (`Cartan.jl:141`) with `Complex{Float64}` fibers. -/
abbrev ComplexMap (m : M) := TensorField m (Complex Float)

/-- Julia `ComplexMap` with `Couple` fibers (`a + b·I` of a pseudoscalar `I`). -/
abbrev CoupleMap (m : M) (V : TensorBundle) := TensorField m (Couple V Float)

/-- Julia `PhasorField` (`Cartan.jl:142`). -/
abbrev PhasorField (m : M) (V : TensorBundle) := TensorField m (Phasor V Float)

/-- Julia `DiagonalField` (`Cartan.jl:136`): a field of diagonal operators of the layout `l`. -/
abbrev DiagonalField (m : M) (V : TensorBundle) (l : Layout) := TensorField m (DiagonalOperator V l Float)

/-- Julia `EndomorphismField` (`Cartan.jl:137`): a field of linear maps `V → V`. -/
abbrev EndomorphismField (m : M) (V : TensorBundle) := TensorField m (Endomorphism V (.chain 1) Float)

/-- Julia `OutermorphismField` (`Cartan.jl:138`). -/
abbrev OutermorphismField (m : M) (V : TensorBundle) := TensorField m (Outermorphism V V Float)

end Fibers

section Bases

variable {N n : Nat} {P G : Type}

/-- Julia `IntervalMap` (`Cartan.jl:123`): a field over an interval (a 1-D grid of real points). -/
abbrev IntervalMap (b : GridBundle 1 Float G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `RealFunction` (`Cartan.jl:128`): a real field over an interval. -/
abbrev RealFunction (b : GridBundle 1 Float G) := TensorField b Float

/-- Julia `AbstractCurve` (`Cartan.jl:131`): chains over an interval. -/
abbrev AbstractCurve (b : GridBundle 1 Float G) (V : TensorBundle) := TensorField b (Chain V 1 Float)

/-- Julia `PlaneCurve` (`Cartan.jl:129`): an `AbstractCurve` whose chains have two components. -/
abbrev PlaneCurve (b : GridBundle 1 Float G) (V : TensorBundle) := AbstractCurve b V

/-- Julia `SpaceCurve` (`Cartan.jl:130`): an `AbstractCurve` whose chains have three components. -/
abbrev SpaceCurve (b : GridBundle 1 Float G) (V : TensorBundle) := AbstractCurve b V

/-- Julia `RectangleMap` (`Cartan.jl:124`): a field over a 2-D grid. -/
abbrev RectangleMap (b : GridBundle 2 P G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `HyperrectangleMap` (`Cartan.jl:125`): a field over a 3-D grid. -/
abbrev HyperrectangleMap (b : GridBundle 3 P G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `ParametricMap` (`Cartan.jl:126`): a field over an `N`-D grid. -/
abbrev ParametricMap (b : GridBundle N P G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `SurfaceGrid` (`Cartan.jl:132`): a real field over a 2-D grid. -/
abbrev SurfaceGrid (b : GridBundle 2 P G) := TensorField b Float

/-- Julia `VolumeGrid` (`Cartan.jl:133`): a real field over a 3-D grid. -/
abbrev VolumeGrid (b : GridBundle 3 P G) := TensorField b Float

/-- Julia `ScalarGrid` (`Cartan.jl:134`): a real field over an `N`-D grid. -/
abbrev ScalarGrid (b : GridBundle N P G) := TensorField b Float

/-- Julia `SimplexMap` (`Cartan.jl:120`): a field over the vertices of a simplex bundle. -/
abbrev SimplexMap (b : SimplexBundle n P G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `ScalarMap` (`Cartan.jl:118`): a real `SimplexMap`. -/
abbrev ScalarMap (b : SimplexBundle n P G) := TensorField b Float

/-- Julia `FaceMap` (`Cartan.jl:121`): a field over the elements (a face bundle). -/
abbrev FaceMap (b : FaceBundle n P G) (F : Type) [FlatFiber F] := TensorField b F

/-- Julia `ElementMap` (`Cartan.jl:119`) over a discontinuous bundle (its simplex form is
`SimplexMap`). -/
abbrev DiscontinuousMap (b : DiscontinuousBundle n P G) (F : Type) [FlatFiber F] := TensorField b F

end Bases

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {F : Type} [FlatFiber F]

/-- Julia `domain(t) = base(t)`. -/
@[inline] def domain (_ : TensorField m F) : M := m

/-- Julia `codomain(t) = fiber(t)`: the fibers, boxed. -/
@[inline] def codomain (t : TensorField m F) : Array F := t.fiberArray

/-- Julia `isextrinsic(t)`: `false` for every field here (no extrinsic metric is modelled). -/
@[inline] def isextrinsic (_ : TensorField m F) : Bool := false

end TensorField

end Cartan
