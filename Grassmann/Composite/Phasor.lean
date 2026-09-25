/-
The complex-like accessors of couples and phasors (Grassmann.jl `src/multivectors.jl:818-1077`;
port-notes/grassmann-composite.md §4.17):

| Julia | here |
|---|---|
| `realvalue(z)`, `imagvalue(z)`, `reim(z)` | `Couple.realvalue`/`imagvalue`/`reim`, `Phasor.realvalue` (`radius`), `Phasor.imagvalue` (the angle's coefficient) |
| `amplitude(z)`, `phase(z)`, `unitangle(z)` | `Phasor.amplitude` (`z.amp`), `phase = 0` (a real amplitude), `unitangle` (the angle's unit blade), and `amplitude = radius` of the other kinds |
| `radius(z)` | `Chain`, `Single`, `Multivector`: `abs` as a number |
| `angle(z::Chain)` | `angle(complexify(z))` of a plane vector |
| `polarize(t)` | `Single`: `1 ∠ t` (`value ∠ 0` for a scalar) |
| `vectorize(z)` | `Couple.vectorizeChain`/`Phasor.vectorizeChain`: a vector of the subspace of the blade (Julia's `_subspace(V, B)`, `Chain{V(B),1}(re, im)`) |
| `Complex(m::Imaginary)`, `Couple(m::Imaginary)` | `Half.toComplex`, `Half.toCouple` (a spinor of a plane: `(⟨m⟩₀, ⟨m⟩₂)` on the pseudoscalar) |
| `a ∠ θ` | the notation `a ∠ θ` (scoped in `Grassmann`) for a real amplitude and an angle given as a couple or a term |
| `hyperplanes(V)`, `𝕚`, `𝕛`, `𝕜` | `Composite.hyperplanes` (`I ⟑ v_k`), and the quaternion units of `ℝ3` |
| `isdiag(T)` | `TensorOperator.isdiag` |

Not provided: phasors with a non-real amplitude or a non-blade angle (Julia's `amp ⊘ exp(angle/2)`
`complexify` and the 2-argument call `z(t, θ)` produce them): `Phasor V α` stores a real amplitude
and a couple angle.
-/
import Grassmann.Composite.Norm
import Grassmann.Composite.Project

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle} {α : Type} [Coeff α]

namespace Couple

/-- Julia `realvalue(z::Couple)` (`src/multivectors.jl:827`). -/
@[inline] def realvalue (z : Couple V α) : α := z.re

/-- Julia `imagvalue(z::Couple)` (`src/multivectors.jl:828`). -/
@[inline] def imagvalue (z : Couple V α) : α := z.im

/-- Julia `reim(z::Couple) = (realvalue(z), imagvalue(z))` (`src/multivectors.jl:830`). -/
@[inline] def reim (z : Couple V α) : α × α := (z.re, z.im)

/-- Julia `unitangle(z)` of a couple read as a phasor: its unit blade. -/
@[inline] def unitangle (z : Couple V α) : Single V (popcount z.bits) α := ⟨z.bits, Coeff.one⟩

/-- Julia `vectorize(z::Couple{V,B}) = Chain{_subspace(V,B),1}(re, im)`
(`src/multivectors.jl:1068`): the coordinates `(re, im)` as a vector of the subspace of the
blade's generators (a grade-2 blade: the plane `V(i, j)`; other entries zero). -/
@[inline] def vectorizeChain (z : Couple V α) : Chain (Forms.restrict V z.bits) 1 α :=
  ⟨Values.ofFn fun i => if i.1 = 0 then z.re else if i.1 = 1 then z.im else Coeff.zero⟩

/-- Julia `amplitude(z) = radius(z)` for a couple (`src/multivectors.jl:903`). -/
@[inline] def amplitude (z : Couple V Float) : Float := z.radius

/-- Julia `phase(z) = 0` of a couple (not a phasor, `src/multivectors.jl:900`). -/
@[inline] def phase (_ : Couple V Float) : Float := 0

end Couple

namespace Phasor

/-- Julia `amplitude(z::Phasor) = z.v` (`src/multivectors.jl:902`). -/
@[inline] def amplitude (z : Phasor V α) : α := z.amp

/-- Julia `phase(z::Phasor{V,B,<:Real}) = 0` (`src/multivectors.jl:895`): the amplitude is real. -/
@[inline] def phase (_ : Phasor V α) : α := Coeff.zero

/-- Julia `unitangle(z::Phasor{V,<:TensorTerm}) = basis(angle(z))` (`src/multivectors.jl:884`). -/
@[inline] def unitangle (z : Phasor V α) : Single V (popcount z.angle.bits) α := ⟨z.angle.bits, Coeff.one⟩

/-- Julia `realvalue(z::Phasor) = Real(radius(z))` (`src/multivectors.jl:858`). -/
@[inline] def realvalue (z : Phasor V Float) : Float := z.radius

/-- Julia `imagvalue(z::Phasor) = Real(angle(z) + phase(z)·unitangle(z))`
(`src/multivectors.jl:859`): the angle's coefficient (the phase of a real amplitude is `0`). -/
@[inline] def imagvalue (z : Phasor V Float) : Float := z.angle.im + z.phase

/-- Julia `vectorize(z::Phasor{V,<:TensorTerm}) = Chain{_subspace(V, unitangle(z)),1}(amplitude,
angle)` (`src/multivectors.jl:1069`). -/
@[inline] def vectorizeChain (z : Phasor V α) : Chain (Forms.restrict V z.angle.bits) 1 α :=
  ⟨Values.ofFn fun i => if i.1 = 0 then z.amp else if i.1 = 1 then z.angle.im else Coeff.zero⟩

end Phasor

/-- An angle for Julia's `a ∠ θ`: a couple, or a term (read as `0 + θ`). -/
class PhasorAngle (X : Type) (V : outParam TensorBundle) (α : outParam Type) where
  /-- The angle as a couple. -/
  toCouple : X → Couple V α

instance : PhasorAngle (Couple V α) V α := ⟨id⟩
instance {G : Nat} : PhasorAngle (Single V G α) V α := ⟨fun s => ⟨s.bits, Coeff.zero, s.val⟩⟩

/-- Julia `∠(a, θ) = Phasor(a, θ)` (`src/multivectors.jl:861`). -/
@[inline] def phasorOf {X : Type} [PhasorAngle X V α] (a : α) (θ : X) : Phasor V α :=
  ⟨a, PhasorAngle.toCouple θ⟩

/-- Julia's `a ∠ θ` (`const ∠ = Phasor`). -/
scoped infixr:67 " ∠ " => phasorOf

namespace Single

variable {G : Nat}

/-- Julia `polarize(m::TensorTerm{V})` (`src/multivectors.jl:1060-1063`): `1 ∠ m` for a
term of positive grade, `value(m) ∠ 0` for a scalar. -/
@[inline] def polarize (s : Single V G α) : Phasor V α :=
  if G == 0 || s.bits == 0 then ⟨s.val, ⟨0, Coeff.zero, Coeff.zero⟩⟩
  else ⟨Coeff.one, ⟨s.bits, Coeff.zero, s.val⟩⟩

/-- Julia `radius(z::TensorAlgebra) = Real(abs(z))` (`src/multivectors.jl:906`). -/
@[inline] def radius (s : Single V G Float) : Float := s.absF

end Single

namespace Chain

variable {G : Nat} [Kernels V]

/-- Julia `radius(z::TensorAlgebra) = Real(abs(z))` (`src/multivectors.jl:906`). -/
@[inline] def radius (c : Chain V G Float) : Float := c.absF

/-- Julia `angle(z::Chain) = angle(complexify(z))` (`src/multivectors.jl:890`) of a plane
vector (`complexify`: the couple `t₁ + t₂·I`). -/
@[inline] def angle (c : Chain V 1 Float) : Couple V Float := (Chain.complexify c).angle

end Chain

namespace Multivector

variable [Kernels V]

/-- Julia `radius(z::TensorAlgebra) = Real(abs(z))` (`src/multivectors.jl:906`): the scalar
of Julia's `abs` (`√⟨~m m⟩₀`). -/
@[inline] def radius (m : Multivector V Float) : Float := getD (Multivector.abs m).v 0

end Multivector

namespace Half

/-- Julia `Complex(m::Imaginary) = Complex(value(m)...)` (`src/multivectors.jl:991`): a spinor
of a plane (`Imaginary{V,T} = Spinor{V,T,2}`) as `⟨m⟩₀ + ⟨m⟩₂·i`. -/
@[inline] def toComplex (s : Half V false α) : Complex α := ⟨getD s.v 0, getD s.v 1⟩

/-- Julia `Couple(m::Imaginary{V}) = Couple{V,Submanifold(V)}(Complex(m))`
(`src/multivectors.jl:993`): the couple on the pseudoscalar. -/
@[inline] def toCouple (s : Half V false α) : Couple V α := ⟨pseudoMask V, getD s.v 0, getD s.v 1⟩

end Half

/-! ## Hyperplanes -/

namespace Composite

/-- Julia `hyperplanes(V) = [I ⟑ v_k | k = 1 … rank(V) - diffvars(V)]` (`src/Grassmann.jl:62`,
`UniformScaling{Bool}(false) * getbasis(V, 1 << k)`): the pseudoscalar times each basis
vector, a term of grade `n - 1` (`hyperplanes(ℝ^3) = [v₂₃, -v₁₃, v₁₂]`,
`hyperplanes(ℝ^2) = [-v₂, v₁]`). -/
def hyperplanes (V : TensorBundle) : List (Single V (V.n - 1) Float) :=
  (List.range (V.n - V.diffvars)).map fun k =>
    let (c, b) := bladeMul V (pseudoMask V) ((1 : UInt64) <<< k.toUInt64)
    ⟨b, c⟩

end Composite

/-- Julia `𝕚 = hyperplanes(ℝ3)[1] = v₂₃` (`src/Grassmann.jl:71`): the quaternion unit `i`. -/
def 𝕚 : Single ℝ3 2 Float := ⟨6, 1⟩

/-- Julia `𝕛 = hyperplanes(ℝ3)[2] = -v₁₃`. -/
def 𝕛 : Single ℝ3 2 Float := ⟨5, -1⟩

/-- Julia `𝕜 = hyperplanes(ℝ3)[3] = v₁₂`. -/
def 𝕜 : Single ℝ3 2 Float := ⟨3, 1⟩

namespace TensorOperator

variable {W : TensorBundle} {ld lc : DirectSum.Layout}

/-- Julia `LinearAlgebra.isdiag(T)` on an operator's matrix: every entry off the diagonal is
zero (`Coeff.isZero`). -/
def isdiag (T : TensorOperator V ld W lc α) : Bool :=
  let r := lc.size W.n
  let c := ld.size V.n
  (List.range c).all fun j => (List.range r).all fun i => i == j || Coeff.isZero (T.entry i j)

end TensorOperator

end Grassmann
