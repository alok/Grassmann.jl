/-
Complex-like two-term elements (Julia `Couple{V,B,T}`, `PseudoCouple{V,B,T}`,
`Phasor{V,B,T}`; `Grassmann.jl src/multivectors.jl:656-939`;
port-notes/grassmann-types.md §3.3, §4.1, §4.8).

* `Couple V α` is `re + im·e_B` (a scalar plus one blade);
* `PseudoCouple V α` is `re·e_B + im·I` (one blade plus the pseudoscalar
  `I = e_{1…n}`, the full mask);
* `Phasor V α` is `amp ∠ angle`, an amplitude and a `Couple` angle
  (Julia allows any angle type; DESIGN.md §4.2 fixes it to a `Couple`).

As DESIGN.md §4.2 prescribes, the blade `B` is runtime data. A degenerate
`Couple` with `B = 0` (Julia `Couple{V,One(V)}`) puts both parts on the scalar,
and a `PseudoCouple` with `B = I` both on the pseudoscalar
(oracle-schema.md §7.1): their dense values are `re + im` on that blade.
-/
import Grassmann.Types.Multivector

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- `re + im·e_bits` (Julia `Couple{V,B}`). -/
structure Couple (V : TensorBundle) (α : Type) where
  /-- The blade `B`. -/
  bits : UInt64
  /-- The scalar part (Julia `realvalue`). -/
  re : α
  /-- The coefficient of `B` (Julia `imagvalue`). -/
  im : α
  deriving BEq, DecidableEq, Hashable, Repr

/-- `re·e_bits + im·I` (Julia `PseudoCouple{V,B}`). -/
structure PseudoCouple (V : TensorBundle) (α : Type) where
  /-- The blade `B`. -/
  bits : UInt64
  /-- The coefficient of `B` (Julia `realvalue`). -/
  re : α
  /-- The coefficient of the pseudoscalar `I` (Julia `imagvalue`). -/
  im : α
  deriving BEq, DecidableEq, Hashable, Repr

/-- `amp ∠ angle` (Julia `Phasor{V,B,T}`, `src/multivectors.jl:852-939`): the
element `amp · exp(angle)` (for scalar-like angles). Its evaluation needs `exp`,
which belongs to the composite-function stage; here it is a plain carrier. -/
structure Phasor (V : TensorBundle) (α : Type) where
  /-- The amplitude (Julia `amplitude(z)`). -/
  amp : α
  /-- The angle (Julia `angle(z)`). -/
  angle : Couple V α
  deriving BEq, DecidableEq, Repr

namespace Couple

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `Couple{V,B}(re, im)` for a unit blade `B`. -/
@[inline] def ofBlade {G : Nat} (b : Submanifold V G) (re im : α) : Couple V α := ⟨b.bits, re, im⟩

/-- Julia `Couple(re, im)` with no space: `V = ℝ²`, `B = v₁₂` (`src/multivectors.jl:668`);
here the pseudoscalar of the given `V`. -/
@[inline] def ofComplex (re im : α) : Couple V α := ⟨lowMask V.n, re, im⟩

/-- The zero couple on blade `B`. -/
@[inline] def zero (b : UInt64 := 0) : Couple V α := ⟨b, Coeff.zero, Coeff.zero⟩

/-- Julia `one(::Couple)`: `(1, 0)`. -/
@[inline] def one (b : UInt64 := 0) : Couple V α := ⟨b, Coeff.one, Coeff.zero⟩

/-- Julia `scalar(z)` as a `Single`. -/
@[inline] def scalarPart (z : Couple V α) : Single V 0 α := ⟨0, z.re⟩

/-- Julia `imaginary(z)`: `im·e_B` (its grade is runtime, so it is returned as a
`Single` of grade `popcount B` wrapped in a sigma pair). -/
@[inline] def imaginary (z : Couple V α) : (G : Nat) × Single V G α := ⟨popcount z.bits, ⟨z.bits, z.im⟩⟩

/-- The dense coefficients (Julia `Multivector(z)`). -/
def toMultivector (z : Couple V α) : Multivector V α :=
  let r := Leibniz.basisRank V.n z.bits
  Multivector.ofFn fun i =>
    if i.1 = 0 && r = 0 then z.re + z.im
    else if i.1 = 0 then z.re else if i.1 = r then z.im else Coeff.zero

instance [Inhabited α] : Inhabited (Couple V α) := ⟨⟨0, default, default⟩⟩

instance : AbstractTensors.TensorMixed (Couple V α) TensorBundle V α where

end Couple

namespace PseudoCouple

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `PseudoCouple{V,B}(re, im)` for a unit blade `B`. -/
@[inline] def ofBlade {G : Nat} (b : Submanifold V G) (re im : α) : PseudoCouple V α := ⟨b.bits, re, im⟩

/-- The zero pseudo-couple on blade `B`. -/
@[inline] def zero (b : UInt64 := 0) : PseudoCouple V α := ⟨b, Coeff.zero, Coeff.zero⟩

/-- The pseudoscalar mask `I` of `V` (all `n` generators). -/
@[inline] def pseudoBits : UInt64 := lowMask V.n

/-- The dense coefficients (Julia `Multivector(z)`). -/
def toMultivector (z : PseudoCouple V α) : Multivector V α :=
  let r := Leibniz.basisRank V.n z.bits
  let top := 2 ^ V.n - 1
  Multivector.ofFn fun i =>
    if i.1 = top && r = top then z.re + z.im
    else if i.1 = r then z.re else if i.1 = top then z.im else Coeff.zero

instance [Inhabited α] : Inhabited (PseudoCouple V α) := ⟨⟨0, default, default⟩⟩

instance : AbstractTensors.TensorMixed (PseudoCouple V α) TensorBundle V α where

end PseudoCouple

namespace Phasor

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `Phasor(amp, angle)`. -/
@[inline] def mk' (amp : α) (angle : Couple V α) : Phasor V α := ⟨amp, angle⟩

/-- Julia `zero(::Phasor)`: zero amplitude, zero angle on the same blade. -/
@[inline] def zero (z : Phasor V α) : Phasor V α := ⟨Coeff.zero, Couple.zero z.angle.bits⟩

/-- Julia `one(::Phasor)`: unit amplitude, zero angle on the same blade. -/
@[inline] def one (z : Phasor V α) : Phasor V α := ⟨Coeff.one, Couple.zero z.angle.bits⟩

/-- Julia `-z = Phasor(-amp, angle)` (`src/products.jl:479-502`). -/
@[inline] def neg (z : Phasor V α) : Phasor V α := ⟨-z.amp, z.angle⟩

/-- Julia `z₁ * z₂ = Phasor(amp₁·amp₂, angle₁ + angle₂)`, defined when the angles
share their blade (or one of them has a zero imaginary part); `none` otherwise
(the angle sum is then not a `Couple`). -/
def mul? (a b : Phasor V α) : Option (Phasor V α) :=
  let θa := a.angle
  let θb := b.angle
  if θa.bits == θb.bits || Coeff.isZero θb.im then
    some ⟨a.amp * b.amp, ⟨θa.bits, θa.re + θb.re, θa.im + θb.im⟩⟩
  else if Coeff.isZero θa.im then
    some ⟨a.amp * b.amp, ⟨θb.bits, θa.re + θb.re, θb.im⟩⟩
  else none

instance [Inhabited α] : Inhabited (Phasor V α) := ⟨⟨default, default⟩⟩

end Phasor

end Grassmann
