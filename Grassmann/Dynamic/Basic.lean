/-
The dynamic element type `TA V α` (DESIGN.md §4.3; port-notes/grassmann-types.md
§3, §4.1-4.2, §8.1): one Lean type for every Julia `TensorAlgebra{V}` value, with
the result *kind* decided at runtime exactly as Julia's method dispatch decides
the result *type*.

| constructor | Julia type | dense support |
|---|---|---|
| `zero` | `Zero{V}` (`𝟎`) | none |
| `one` | `One{V}` = `Submanifold{V,0,0}` (`v`) | the scalar, value `1` |
| `infinity` | `Infinity{V}` (`∞`) | none (not a finite element) |
| `blade b` | a unit basis blade `Submanifold{V,G,B}`, `b ≠ 0` | `b`, value `1` |
| `single b x` | `Single{V,G,B,T}` (`x·e_b`, `x` may be `0`) | `b` |
| `chain g c` | `Chain{V,g,T}` | the grade-`g` blades |
| `couple b re im` | `Couple{V,B,T}` = `re + im·e_b` | `1`, `b` |
| `pseudo b re im` | `PseudoCouple{V,B,T}` = `re·e_b + im·I` | `b`, `I` |
| `spinor s` / `cospinor s` | `Spinor{V,T}` / `CoSpinor{V,T}` | even / odd grades |
| `multi m` | `Multivector{V,T}` | everything |
| `phasor amp angle` | `Phasor{V,B,T}` = `amp ∠ angle` | not linear (needs `exp`) |

The *linear* kinds (all but `infinity` and `phasor`) have a dense value
`toDense : TA V α → Multivector V α`; the arithmetic of `Grassmann.Dynamic.Arith`
is proved to commute with it (`Grassmann.Dynamic.Laws`), so every branch of
Julia's representation lattice computes the right element and the lattice only
decides *which constructor* holds it.

The dense value is defined through the coefficient function `coeff x β` (the
coefficient of blade `β`) read at the blades of the multivector layout. That
definition needs no index bijection: containers are read with their layout's
`rank` exactly as the static layer reads them (`Chain.coeff`, `Half.coeff`), and a
`Multivector` is its own dense value.
-/
import Grassmann.Types.Convert

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- A Julia `TensorAlgebra{V}` value with coefficients in `α` (DESIGN.md §4.3). -/
inductive TA (V : TensorBundle) (α : Type) [Coeff α] : Type where
  /-- Julia `Zero{V}` (prints `𝟎`). -/
  | zero
  /-- Julia `One{V}`, the unit scalar blade (prints `v`). -/
  | one
  /-- Julia `DirectSum.Infinity{V}` (prints `∞`). -/
  | infinity
  /-- A unit basis blade of grade `≥ 1` (Julia `Submanifold{V,G,B}`). -/
  | blade (b : UInt64)
  /-- `x·e_b` (Julia `Single{V,G,B,T}`); a zero value stays a `Single`. -/
  | single (b : UInt64) (x : α)
  /-- A grade-`g` chain (Julia `Chain{V,g,T}`). -/
  | chain (g : Nat) (c : Chain V g α)
  /-- `re + im·e_b` (Julia `Couple{V,B,T}`). -/
  | couple (b : UInt64) (re im : α)
  /-- `re·e_b + im·I` (Julia `PseudoCouple{V,B,T}`). -/
  | pseudo (b : UInt64) (re im : α)
  /-- The even grades (Julia `Spinor{V,T}`). -/
  | spinor (s : Spinor V α)
  /-- The odd grades (Julia `CoSpinor{V,T}`). -/
  | cospinor (s : CoSpinor V α)
  /-- Every grade (Julia `Multivector{V,T}`). -/
  | multi (m : Multivector V α)
  /-- `amp ∠ angle` (Julia `Phasor{V,B,T}`, `src/multivectors.jl:852-939`): the element
  `amp · exp(angle)`; the angle is itself an element (a term or a `Couple` in practice). -/
  | phasor (amp : α) (angle : TA V α)

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α]

instance : Inhabited (TA V α) := ⟨.zero⟩

/-! ## Kinds -/

/-- The result kind of a dynamic element: Julia's concrete type constructor
(oracle-schema.md §7). -/
inductive Kind where
  /-- `Zero`. -/
  | zero
  /-- `One`. -/
  | one
  /-- `Infinity`. -/
  | infinity
  /-- `Submanifold` (a unit blade of grade ≥ 1). -/
  | submanifold
  /-- `Single`. -/
  | single
  /-- `Chain`. -/
  | chain
  /-- `Spinor`. -/
  | spinor
  /-- `CoSpinor`. -/
  | cospinor
  /-- `Multivector`. -/
  | multivector
  /-- `Couple`. -/
  | couple
  /-- `PseudoCouple`. -/
  | pseudoCouple
  /-- `Phasor`. -/
  | phasor
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Julia's name of the kind (the oracle's `kind` tag). -/
def Kind.name : Kind → String
  | .zero => "Zero" | .one => "One" | .infinity => "Infinity" | .submanifold => "Submanifold"
  | .single => "Single" | .chain => "Chain" | .spinor => "Spinor" | .cospinor => "CoSpinor"
  | .multivector => "Multivector" | .couple => "Couple" | .pseudoCouple => "PseudoCouple"
  | .phasor => "Phasor"

instance : ToString Kind := ⟨Kind.name⟩

/-- The kind of an element. -/
def kind : TA V α → Kind
  | zero => .zero | one => .one | infinity => .infinity | blade _ => .submanifold
  | single .. => .single | chain .. => .chain | couple .. => .couple | pseudo .. => .pseudoCouple
  | spinor _ => .spinor | cospinor _ => .cospinor | multi _ => .multivector | phasor .. => .phasor

/-- Julia's storage grade `G` of a graded element (`Zero`/`Infinity`: `0`; a term:
the popcount of its blade; a chain: its grade); `none` for mixed kinds. -/
def grade? : TA V α → Option Nat
  | zero | one | infinity => some 0
  | blade b | single b _ => some (popcount b)
  | chain g _ => some g
  | _ => none

/-- The blade `B` of a kind that carries one (`One` has `0`). -/
def bits? : TA V α → Option UInt64
  | one => some 0
  | blade b | single b _ | couple b .. | pseudo b .. => some b
  | _ => none

/-- A *linear* element: every kind but `infinity` and `phasor`, which have no
dense value (`toDense` sends them to `0`). The arithmetic laws hold on linear
elements. -/
def IsLinear : TA V α → Prop
  | infinity | phasor .. => False
  | _ => True

instance (x : TA V α) : Decidable x.IsLinear := by
  cases x <;> simp only [IsLinear] <;> infer_instance

/-- A *term* (Julia `TensorTerm`, apart from `Zero`/`Infinity`): its blade and value. -/
def term? : TA V α → Option (UInt64 × α)
  | one => some (0, Coeff.one)
  | blade b => some (b, Coeff.one)
  | single b x => some (b, x)
  | _ => none

/-! ## Space options and blades -/

/-- Julia's guard `!istangent(V) && !hasconformal(V)` under which sums of terms
may form a `Couple`/`PseudoCouple` (`src/algebra.jl:747-780`). -/
@[inline] def coupleOK (V : TensorBundle) : Bool := !V.istangent && !V.hasconformal

/-- The pseudoscalar blade `I` (Julia `basis(V)`): every generator. -/
@[inline] def pseudoBits (V : TensorBundle) : UInt64 := lowMask V.n

/-- Whether `b` is a blade of `V` (Julia's `b < 2ⁿ`). -/
@[inline] def valid (V : TensorBundle) (b : UInt64) : Bool := Layout.full.contains V.n b

/-- The blade at 0-based position `i` of the multivector layout. -/
@[inline] def fullBlade (n i : Nat) : UInt64 := (Leibniz.indexBasisAll n)[i]!

/-! ## Coefficients and the dense value -/

/-- The coefficient of blade `β` (linear kinds; `infinity`/`phasor` give `0`).
Degenerate couples (`Couple` on the scalar, `PseudoCouple` on `I`) put both parts
on one blade (oracle-schema.md §7.1). -/
def coeff (x : TA V α) (β : UInt64) : α :=
  match x with
  | zero | infinity | phasor .. => Coeff.zero
  | one => if β == 0 then Coeff.one else Coeff.zero
  | blade b => if β == b && valid V b then Coeff.one else Coeff.zero
  | single b v => if β == b && valid V b then v else Coeff.zero
  | chain _ c => c.coeff β
  | couple b re im =>
    if β == 0 then (if b == 0 then re + im else re)
    else if β == b && valid V b then im else Coeff.zero
  | pseudo b re im =>
    if β == b && valid V b then (if b == pseudoBits V then re + im else re)
    else if β == pseudoBits V then im else Coeff.zero
  | spinor s => s.coeff β
  | cospinor s => s.coeff β
  | multi m => m.coeff β

/-- The dense value (Julia `Multivector(x)`, oracle `dense`): a `Multivector` is
itself; any other linear kind is read blade by blade (`coeff`). `infinity` and
`phasor` have no dense value and give `0`. -/
def toDense : TA V α → Multivector V α
  | multi m => m
  | x => Multivector.ofFn fun i => x.coeff (fullBlade V.n i.1)

/-! ## Building containers from coefficient functions -/

/-- The grade-`g` chain whose coefficient at each blade `β` is `f β`. -/
@[inline] def chainOf (V : TensorBundle) (g : Nat) (f : UInt64 → α) : Chain V g α :=
  Chain.ofFn fun j => f ((Leibniz.indexBasis V.n g)[j.1]!)

/-- The half of parity `p` whose coefficient at each blade `β` is `f β`. -/
@[inline] def halfOf (V : TensorBundle) (p : Bool) (f : UInt64 → α) : Half V p α :=
  Half.ofFn fun j => f (((halfLayout p).blades V.n)[j.1]!)

/-- The multivector whose coefficient at each blade `β` is `f β`. -/
@[inline] def multiOf (V : TensorBundle) (f : UInt64 → α) : Multivector V α :=
  Multivector.ofFn fun i => f (fullBlade V.n i.1)

/-! ## Views of the static types -/

/-- A static chain as a dynamic element. -/
@[inline] def ofChain {G : Nat} (c : Chain V G α) : TA V α := chain G c

/-- A static half as a dynamic element (`Spinor` or `CoSpinor` by parity). -/
@[inline] def ofHalf {p : Bool} (h : Half V p α) : TA V α :=
  match p, h with
  | false, h => spinor h
  | true, h => cospinor h

/-- A static single as a dynamic element. -/
@[inline] def ofSingle {G : Nat} (s : Single V G α) : TA V α := single s.bits s.val

/-- A unit blade as a dynamic element (`One` for the scalar blade). -/
@[inline] def ofBlade (b : UInt64) : TA V α := if b == 0 then one else blade b

/-- A static couple as a dynamic element. -/
@[inline] def ofCouple (z : Couple V α) : TA V α := couple z.bits z.re z.im

/-- A static pseudo-couple as a dynamic element. -/
@[inline] def ofPseudoCouple (z : PseudoCouple V α) : TA V α := pseudo z.bits z.re z.im

instance {G : Nat} : CoeOut (Chain V G α) (TA V α) := ⟨ofChain⟩
instance {p : Bool} : CoeOut (Half V p α) (TA V α) := ⟨ofHalf⟩
instance : Coe (Multivector V α) (TA V α) := ⟨multi⟩
instance {G : Nat} : CoeOut (Single V G α) (TA V α) := ⟨ofSingle⟩
instance : Coe (Couple V α) (TA V α) := ⟨ofCouple⟩
instance : Coe (PseudoCouple V α) (TA V α) := ⟨ofPseudoCouple⟩

/-! ## Julia's parts and conversions -/

/-- Julia `Single(t)` of a length-one chain (`src/multivectors.jl:149-152`): the
scalar (`G = 0`) or the pseudoscalar term (`volume`, the top blade). -/
def singleOfChain {G : Nat} (c : Chain V G α) : TA V α :=
  let x := getD c.v 0
  if G == 0 then single 0 x else single (pseudoBits V) x

/-- Julia `scalar(z)` of a couple (`src/multivectors.jl:1107`): `Single{V}(re)`. -/
@[inline] def coupleScalar (re : α) : TA V α := single 0 re

/-- Julia `imaginary(z)` (`src/multivectors.jl:1136-1137`): `im·e_B` of a couple,
`re·e_B` of a pseudo-couple. -/
@[inline] def termOf (b : UInt64) (x : α) : TA V α := single b x

/-- Julia `volume(z::PseudoCouple) = Single{V,n,I}(im)` (`src/multivectors.jl:1131`). -/
@[inline] def pseudoVolume (im : α) : TA V α := single (pseudoBits V) im

/-- Julia `Multivector(x)` for every linear kind: the dense value as a `multi`. -/
@[inline] def toMultiTA (x : TA V α) : TA V α := multi x.toDense

/-- Julia `Spinor(t)`/`CoSpinor(t)` of an element supported on one parity: the
half built from the coefficient function (zeros elsewhere). -/
@[inline] def toHalfTA (p : Bool) (x : TA V α) : TA V α := ofHalf (halfOf V p x.coeff)

/-- Julia `multispin(t)` (`src/multivectors.jl:999-1014`): the smallest
spinor-family container of a graded element (`Spinor`/`CoSpinor` by the parity of
its grade), a couple (`Spinor` for an even blade, else `Multivector`) or a
pseudo-couple (`Spinor`/`CoSpinor` when the blade has the parity of the pseudoscalar,
else `Multivector`); halves and multivectors are returned as they are. Julia tests
the parity of `grade(V)`; that is `n` except in tangent spaces, where Julia never
forms a `PseudoCouple` and the pseudoscalar `I` has `n` generators, so `n` is the
parity that keeps the value. -/
def multispin (x : TA V α) : TA V α :=
  match x with
  | spinor _ | cospinor _ | multi _ => x
  | couple b .. => if popcount b % 2 == 0 then toHalfTA false x else toMultiTA x
  | pseudo b .. =>
    if V.n % 2 == 0 && popcount b % 2 == 0 then toHalfTA false x
    else if V.n % 2 == 1 && popcount b % 2 == 1 then toHalfTA true x
    else toMultiTA x
  | chain g _ => toHalfTA (g % 2 == 1) x
  | one | blade _ | single .. => match x.grade? with
    | some g => toHalfTA (g % 2 == 1) x
    | none => x
  | zero | infinity | phasor .. => x

/-! ## Coefficient maps -/

/-- Map the coefficients into another coefficient type (Julia's promotion of the
`valuetype`, e.g. `Int64 → Float64`). Kinds are preserved. -/
def map {β : Type} [Coeff β] (f : α → β) : TA V α → TA V β
  | zero => .zero
  | one => .one
  | infinity => .infinity
  | blade b => .blade b
  | single b x => .single b (f x)
  | chain g c => .chain g (c.map f)
  | couple b re im => .couple b (f re) (f im)
  | pseudo b re im => .pseudo b (f re) (f im)
  | spinor s => .spinor (s.map f)
  | cospinor s => .cospinor (s.map f)
  | multi m => .multi (m.map f)
  | phasor amp θ => .phasor (f amp) (map f θ)

end TA

end Grassmann
