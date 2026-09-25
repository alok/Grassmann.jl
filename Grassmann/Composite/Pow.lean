/-
`^` on the composite element kinds (Julia `Base.:^`, Grassmann.jl `src/algebra.jl:422-470`,
AbstractTensors `AT:326`; port-notes/grassmann-composite.md §4.7).

* `t ^ k` for an integer exponent `k : Nat` or `k : Int`: Julia's `^(v::TensorAlgebra, i::Integer)`
  (the `contraction(~t, t)` shortcut for chains of spaces of dimension `≤ 3`, the complex power
  of an elliptic couple, repeated multiplication below `8`, binary powering above) through the
  kind's `pow`. A negative exponent is `inv(t)^|k|`, Julia's `literal_pow` for a negative
  literal (`v12^-1`); Julia's `^` on a negative *variable* returns `One`/`t` (a defect not
  replicated).
* `t ^ x` for a real exponent `x : Float` where a principal branch is defined: `exp(x·log t)`
  (Julia `Phasor ^ Real = Phasor(amplitude^x, x·angle)`).
* `b ^ t` for a real base (`Float` or a `Nat` literal such as `2 ^ v12`): Julia
  `^(b::Number, t) = exp(t ⟑ log b)` (`AT:326`).

The result kinds are the ones of the kind's `pow`: a chain's powers are multivectors, a term's
are couples (`v12^2 = -1`, `v12^-1 = -v12`), and couples, phasors, spinors and multivectors are
closed.

Lean's `^` elaborator assumes a homogeneous power when nothing else fixes the result type, so
a heterogeneous power needs an expected type (`(v12 ^ 2 : Couple V Float)`,
`(t ^ 3 : Multivector V Float)`), and a literal base its type (`(2 : Nat) ^ v12`); a negative
exponent is written `t ^ (-1 : Int)`.
-/
import Grassmann.Composite.Norm

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

variable {V : TensorBundle} [Kernels V] {G : Nat}

/-! ## Integer exponents -/

instance : HPow (Multivector V Float) Int (Multivector V Float) := ⟨Multivector.pow⟩
instance : HPow (Multivector V Float) Nat (Multivector V Float) := ⟨fun t k => t.pow k⟩
instance : HPow (Half V false Float) Int (Half V false Float) := ⟨Half.pow⟩
instance : HPow (Half V false Float) Nat (Half V false Float) := ⟨fun t k => t.pow k⟩
instance : HPow (Chain V G Float) Int (Multivector V Float) := ⟨Chain.pow⟩
instance : HPow (Chain V G Float) Nat (Multivector V Float) := ⟨fun t k => t.pow k⟩
instance : HPow (Single V G Float) Int (Couple V Float) := ⟨Single.pow⟩
instance : HPow (Single V G Float) Nat (Couple V Float) := ⟨fun t k => t.pow k⟩
instance : HPow (Couple V Float) Int (Couple V Float) := ⟨Couple.pow⟩
instance : HPow (Couple V Float) Nat (Couple V Float) := ⟨fun t k => t.pow k⟩
instance : HPow (Phasor V Float) Int (Phasor V Float) := ⟨Phasor.pow⟩
instance : HPow (Phasor V Float) Nat (Phasor V Float) := ⟨fun t k => t.pow k⟩

/-! ## Real exponents -/

instance : HPow (Multivector V Float) Float (Multivector V Float) := ⟨Multivector.powf⟩
instance : HPow (Half V false Float) Float (Half V false Float) := ⟨Half.powf⟩
instance : HPow (Couple V Float) Float (Couple V Float) := ⟨Couple.powf⟩
instance : HPow (Phasor V Float) Float (Phasor V Float) := ⟨Phasor.powf⟩

/-! ## Real bases -/

instance : HPow Float (Multivector V Float) (Multivector V Float) := ⟨Multivector.rpow⟩
instance : HPow Float (Half V false Float) (Half V false Float) := ⟨Half.rpow⟩
instance : HPow Float (Chain V G Float) (Multivector V Float) := ⟨Chain.rpow⟩
instance : HPow Float (Single V G Float) (Couple V Float) := ⟨Single.rpow⟩
instance : HPow Float (Couple V Float) (Couple V Float) := ⟨Couple.rpow⟩
instance : HPow Nat (Multivector V Float) (Multivector V Float) := ⟨fun b t => Multivector.rpow b.toFloat t⟩
instance : HPow Nat (Half V false Float) (Half V false Float) := ⟨fun b t => Half.rpow b.toFloat t⟩
instance : HPow Nat (Chain V G Float) (Multivector V Float) := ⟨fun b t => Chain.rpow b.toFloat t⟩
instance : HPow Nat (Single V G Float) (Couple V Float) := ⟨fun b t => Single.rpow b.toFloat t⟩
instance : HPow Nat (Couple V Float) (Couple V Float) := ⟨fun b t => Couple.rpow b.toFloat t⟩

end Grassmann
