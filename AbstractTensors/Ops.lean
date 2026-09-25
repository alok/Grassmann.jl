/-
The AbstractTensors operator vocabulary (Julia `AbstractTensors.jl`, AT:257-349,
573-582; port-notes §2.1.4-2.1.6, §8.2-8.3).

Julia declares generic functions (`∧`, `∨`, `⟑`, `⋆`, `contraction`, …) that
downstream packages extend with methods whose result *types* depend on the
argument types (`Chain V G ∧ Chain V H` is a `Chain V (G+H)`). Here each
operator is a heterogeneous class with an `outParam` result, like core
`HMul`, and Grassmann supplies the instances.

The notation (DESIGN §4.4) is `scoped` in `AbstractTensors`: `open
AbstractTensors` to use it. `∧`, `∨`, `×` and `!` **overload** core's `And`,
`Or`, `Prod` and `not` at exactly their precedences, so the parser produces a
choice node and elaboration keeps whichever reading typechecks: Prop `∧`,
type `×` and Bool `!` keep working in files that open the namespace (see
`Tests/AbstractTensors/Notation.lean`). The price is Lean's precedences:
`∧` is 35 and `∨` is 30 (Julia: 12 and 11), so write `(a ∧ b) + c`, and `!`
takes its operand at precedence 40, so `!a * b` is `!(a * b)` (Julia:
`(!a) * b`). Parenthesize every wedge, vee and complement operand when
porting Julia expressions.
-/
import AbstractTensors.Dims
import AbstractTensors.Coeff
import AbstractTensors.Alias
import AbstractLattices.Basic

universe u v w

namespace AbstractTensors

open StaticVectors JuliaBase

/-! ## Kind and parameter classes (port-notes §8.2 item 1)

Julia's abstract type tree `TensorAlgebra{V,T} ⊇ Manifold ⊇ TensorGraded{V,G,T}
⊇ TensorTerm`, `TensorMixed` (AT:27-132) becomes `Prop`-valued classes whose
`outParam`s are the type parameters, so accessors like `Manifold x` are pure
compile-time facts. -/

/-- `X` is a tensor-algebra element type over the manifold `V : M` with scalar
field `T` (Julia `X <: TensorAlgebra{V,T}`, AT:32). -/
class TensorAlgebra (X : Type u) (M : outParam (Type v)) (V : outParam M) (T : outParam (Type w)) :
    Prop where

/-- `X` is homogeneous of grade `G` (Julia `TensorGraded{V,G,T}`, AT:64). -/
class TensorGraded (X : Type u) (M : outParam (Type v)) (V : outParam M) (G : outParam Nat)
    (T : outParam (Type w)) : Prop extends TensorAlgebra X M V T where

/-- `X` is a single-term element: a scaled basis blade (Julia `TensorTerm`, AT:108). -/
class TensorTerm (X : Type u) (M : outParam (Type v)) (V : outParam M) (G : outParam Nat)
    (T : outParam (Type w)) : Prop extends TensorGraded X M V G T where

/-- `X` is a mixed-grade element (Julia `TensorMixed`, AT:124). -/
class TensorMixed (X : Type u) (M : outParam (Type v)) (V : outParam M) (T : outParam (Type w)) :
    Prop extends TensorAlgebra X M V T where

/-- A manifold type whose values know their dimension (Julia `mdims(V)`); the
DirectSum `TensorBundle` provides it. -/
class HasMDims (M : Type v) where
  /-- Number of generators (Julia `mdims`). -/
  mdims : M → Nat

/-- Julia `mdims(M::Int) = M` (AT:163): a bare dimension is its own manifold. -/
instance : HasMDims Nat := ⟨id⟩

section Accessors

variable {X : Type u} {M : Type v} {V : M} {T : Type w}

/-- Julia `Manifold(x)` (AT:136): the manifold value of the type. -/
def Manifold (_ : X) [TensorAlgebra X M V T] : M := V

/-- Julia `valuetype(x)` (AT:221): the scalar field. -/
def valuetype (_ : X) [TensorAlgebra X M V T] : Type w := T

/-- Julia `rank(t)` / `grade(t)` for a graded element (AT:153). -/
def rank {G : Nat} (_ : X) [TensorGraded X M V G T] : Nat := G

/-- Julia `mdims(t)` (AT:161): the number of generators of `Manifold(t)`. -/
def mdims (_ : X) [TensorAlgebra X M V T] [HasMDims M] : Nat := HasMDims.mdims V

/-- Julia `tdims(t) = 1 << mdims(t)` (AT:170). -/
def tdimsOf (_ : X) [TensorAlgebra X M V T] [HasMDims M] : Nat := tdims (HasMDims.mdims V)

/-- Julia `gdims(t) = binomial(mdims(t), G)` for a graded element (AT:179). -/
def gdimsOf {G : Nat} (_ : X) [TensorGraded X M V G T] [HasMDims M] : Nat :=
  gdims (HasMDims.mdims V) G

/-- Julia `isscalar(t) = rank(t) == 0 || iszero(t)` restricted to the static
part: whether the grade is `0` (AT:194). -/
def isScalarGrade {G : Nat} (_ : X) [TensorGraded X M V G T] : Bool := G == 0

end Accessors

/-- Julia `value(t)` (AT:213): the coefficient storage of a tensor (a `Values`
for `Chain`/`Multivector`, the coefficient for a `Single`). Scalars are their
own value. -/
class Value (X : Type u) (Y : outParam (Type v)) where
  /-- The coefficient storage. -/
  value : X → Y

export Value (value)

instance : Value Float Float := ⟨id⟩
instance : Value Int Int := ⟨id⟩
instance : Value Rat Rat := ⟨id⟩
instance {α : Type} : Value (Complex α) (Complex α) := ⟨id⟩

/-! ## Binary products (AT:257-349; port-notes §2.1.6) -/

/-! `Wedge`/`Vee` **are** the AbstractLattices classes `HWedge`/`HVee` (Julia: `∧ === wedge`
and `∨ === vee` are single generic functions owned by AbstractLattices, extended by
AbstractTensors, Grassmann, DeMorgan and Dendriform, `AbstractLattices.jl
src/AbstractLattices.jl:5-9`). The names `Wedge`, `Wedge.wedge`, `wedge`, `Vee`, `Vee.vee`,
`vee` are aliases of `AbstractLattices.HWedge`, `HWedge.wedge`, … (`export_alias`), so an
instance declared as `Wedge A B C` is an `HWedge A B C` instance, and the `∧`/`∨` notation of
AbstractTensors and Grassmann reaches the Bool, truth-table and tree instances too. -/

export_alias Wedge => AbstractLattices.HWedge
export_alias Wedge.wedge => AbstractLattices.HWedge.wedge
export_alias Vee => AbstractLattices.HVee
export_alias Vee.vee => AbstractLattices.HVee.vee

/-- Geometric product `⟑` (Julia `wedgedot`, `times`, `*`). Grassmann gives
tensors both this and `HMul`. -/
class WedgeDot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⟑ b`. -/
  wedgedot : α → β → γ

/-- Anti-geometric product `⟇` (Julia `veedot`, AT:628). -/
class VeeDot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⟇ b`. -/
  veedot : α → β → γ

/-- Right contraction `⋅`, `⨽` (Julia `contraction`, `dot`, `|`, `>`, AT:264). -/
class Contraction (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⋅ b = a ⨽ b`. -/
  contraction : α → β → γ

/-- Expansion / anti-dot `∘` (Julia `expansion`, `antidot`, `codot`, AT:314). -/
class Expansion (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `expansion a b`. -/
  expansion : α → β → γ

/-- Cross product `×` (Julia `LinearAlgebra.cross`, AT:349). -/
class Cross (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a × b`. -/
  cross : α → β → γ

/-- Sandwich `⊘` (Julia `sandwich`, AT:313; Grassmann: `x ⊘ R = R ⟑ x ⟑ R⁻¹`). -/
class Sandwich (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `x ⊘ R`. -/
  sandwich : α → β → γ

/-- Tensor product `⊗` (Julia `⊗`, AT:333). -/
class TensorProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⊗ b`. -/
  tensorProd : α → β → γ

/-- Symmetrized product `⊙` (declared in AT:342, defined by Grassmann). -/
class SymProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⊙ b`. -/
  symProd : α → β → γ

/-- Antisymmetrized product `⊠` (declared in AT:342, defined by Grassmann). -/
class AntiSymProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⊠ b`. -/
  antiSymProd : α → β → γ

export_alias wedge => AbstractLattices.HWedge.wedge
export_alias vee => AbstractLattices.HVee.vee
export WedgeDot (wedgedot)
export VeeDot (veedot)
export Contraction (contraction)
export Expansion (expansion)
export Cross (cross)
export Sandwich (sandwich)
export TensorProd (tensorProd)

/-! ## Unary operations (AT:183-316) -/

/-- Hodge complement `⋆` (Julia `complementrighthodge`, `hodge`, AT:311). -/
class Hodge (α : Type u) (β : outParam (Type v)) where
  /-- `⋆t`. -/
  hodge : α → β

/-- Left complement (Julia `complementleft`, AT:342). -/
class ComplementLeft (α : Type u) (β : outParam (Type v)) where
  /-- `complementleft(t)`. -/
  complementLeft : α → β

/-- Right complement `!` (Julia `complementright`, `complement`, `!`, AT:309). -/
class ComplementRight (α : Type u) (β : outParam (Type v)) where
  /-- `!t`. -/
  complementRight : α → β

/-- Reverse `~` (Julia `reverse`/`~`). Preserves the type (DESIGN §4.2). -/
class Reverse (α : Type u) where
  /-- `~t`. -/
  reverse : α → α

/-- Grade involution (Julia `involute`, postfix `ˣ`). Preserves the type. -/
class Involute (α : Type u) where
  /-- `involute t`. -/
  involute : α → α

/-- Clifford conjugation (Julia `clifford`, AT:342). Preserves the type. -/
class Clifford (α : Type u) where
  /-- `clifford t`. -/
  clifford : α → α

/-- Even part `t₊` (Julia `even`, AT:347). -/
class Even (α : Type u) (β : outParam (Type v)) where
  /-- `t₊`. -/
  even : α → β

/-- Odd part `t₋` (Julia `odd`, AT:348). -/
class Odd (α : Type u) (β : outParam (Type v)) where
  /-- `t₋`. -/
  odd : α → β

/-- Grade-`G` projection (Julia `scalar`, `vector`, `bivector`, `trivector`,
AT:183-196; `t(G)` in Grassmann). -/
class GradeProj (α : Type u) (G : Nat) (β : outParam (Type v)) where
  /-- The grade-`G` part. -/
  proj : α → β

/-- Pseudoscalar-grade projection (Julia `volume`/`pseudoscalar`, AT:203-205). -/
class Volume (α : Type u) (β : outParam (Type v)) where
  /-- The top-grade part. -/
  volume : α → β

export Hodge (hodge)
export ComplementLeft (complementLeft)
export ComplementRight (complementRight)
export Involute (involute)
export Clifford (clifford)
export Even (even)
export Odd (odd)
export Volume (volume)

/-- Julia `scalar(t)` (AT:192): the grade-0 part. -/
abbrev scalar {α : Type u} {β : Type v} [GradeProj α 0 β] : α → β := GradeProj.proj (G := 0)
/-- Julia `vector(t)`: the grade-1 part. -/
abbrev vector {α : Type u} {β : Type v} [GradeProj α 1 β] : α → β := GradeProj.proj (G := 1)
/-- Julia `bivector(t)`: the grade-2 part. -/
abbrev bivector {α : Type u} {β : Type v} [GradeProj α 2 β] : α → β := GradeProj.proj (G := 2)
/-- Julia `trivector(t)`: the grade-3 part. -/
abbrev trivector {α : Type u} {β : Type v} [GradeProj α 3 β] : α → β := GradeProj.proj (G := 3)

/-! ## Derived operations (AT:257-261, 349, 559-569) -/

/-- Left contraction `a ⨼ b = contraction(b, a)` (AT:259). -/
@[inline] def leftContraction {α : Type u} {β : Type v} {γ : Type w} [Contraction β α γ]
    (a : α) (b : β) : γ := contraction b a

/-- Reverse-geometric product `a ∗ b = (~a) ⟑ b` (AT:257). -/
@[inline] def reverseProduct {α : Type u} {β : Type v} {γ : Type w} [Reverse α] [WedgeDot α β γ]
    (a : α) (b : β) : γ := wedgedot (Reverse.reverse a) b

/-- Scalar product `a ⊛ b = scalar(contraction(a, b))` (AT:258). -/
@[inline] def scalarProduct {α : Type u} {β : Type v} {γ δ : Type w} [Contraction α β γ]
    [GradeProj γ 0 δ] (a : α) (b : β) : δ := scalar (contraction a b)

/-- Julia `a << b = contraction(b, ~a)` (AT:260). -/
@[inline] def shiftLeftContraction {α : Type u} {β : Type v} {γ : Type w} [Reverse α]
    [Contraction β α γ] (a : α) (b : β) : γ := contraction b (Reverse.reverse a)

/-- Julia `a >> b = contraction(~a, b)` (AT:261). -/
@[inline] def shiftRightContraction {α : Type u} {β : Type v} {γ : Type w} [Reverse α]
    [Contraction α β γ] (a : α) (b : β) : γ := contraction (Reverse.reverse a) b

/-- Julia `cross(a, b) = hodge(a ∧ b)` (AT:349), the default `×` for anything
with a wedge and a Hodge complement. -/
instance (priority := low) instCrossOfWedgeHodge {α : Type u} {β : Type v} {γ δ : Type w}
    [Wedge α β γ] [Hodge γ δ] : Cross α β δ := ⟨fun a b => hodge (wedge a b)⟩

/-- Julia `@co f(x)` / `@pseudo f(x)` (AT:500-530): the complement-conjugated
function `complementleft ∘ f ∘ complementright`. -/
@[inline] def co {α : Type u} {β γ : Type v} {δ : Type w} [ComplementRight α β]
    [ComplementLeft γ δ] (f : β → γ) (x : α) : δ :=
  complementLeft (f (complementRight x))

/-- Julia `@co f(a, b)`: `complementleft(f(!a, !b))`. -/
@[inline] def co₂ {α α' : Type u} {β β' γ : Type v} {δ : Type w} [ComplementRight α β]
    [ComplementRight α' β'] [ComplementLeft γ δ] (f : β → β' → γ) (x : α) (y : α') : δ :=
  complementLeft (f (complementRight x) (complementRight y))

/-- Julia `@pseudo` is the same combinator as `@co`. -/
abbrev pseudo {α : Type u} {β γ : Type v} {δ : Type w} [ComplementRight α β] [ComplementLeft γ δ]
    (f : β → γ) (x : α) : δ := co f x

/-- Julia `cosandwich(x, R) = complementleft(sandwich(!x, !R))` (AT:559), alias
`pseudosandwich`. -/
@[inline] def cosandwich {α α' : Type u} {β β' γ : Type v} {δ : Type w} [ComplementRight α β]
    [ComplementRight α' β'] [Sandwich β β' γ] [ComplementLeft γ δ] (x : α) (R : α') : δ :=
  co₂ sandwich x R

/-! ## Uniform scaling (Julia `LinearAlgebra.UniformScaling`, AT:287-316)

`λI` is a dimension-free pseudoscalar: `V(λI)` is `λ` times the unit
pseudoscalar of `V`. The complement of a scalar is a uniform scaling and
vice versa. -/

/-- Julia `UniformScaling(λ)`, written `λI` (`λ` is reserved in Lean). -/
structure UniformScaling (α : Type u) where
  /-- The scale `λ`. -/
  val : α
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Julia `!x = x·I` for a real scalar (AT:303). -/
instance : ComplementRight Float (UniformScaling Float) := ⟨UniformScaling.mk⟩
instance : ComplementRight Int (UniformScaling Int) := ⟨UniformScaling.mk⟩
instance : ComplementRight Rat (UniformScaling Rat) := ⟨UniformScaling.mk⟩
instance {α : Type} : ComplementRight (Complex α) (UniformScaling (Complex α)) := ⟨UniformScaling.mk⟩
/-- Julia `hodge(x) = x·I` for a scalar (AT:303). -/
instance : Hodge Float (UniformScaling Float) := ⟨UniformScaling.mk⟩
instance : Hodge Int (UniformScaling Int) := ⟨UniformScaling.mk⟩
instance : Hodge Rat (UniformScaling Rat) := ⟨UniformScaling.mk⟩
instance {α : Type} : Hodge (Complex α) (UniformScaling (Complex α)) := ⟨UniformScaling.mk⟩
/-- Julia `!(λI) = λ` (AT:316; `Bool` scales become `0`/`1`). -/
instance {α : Type u} : ComplementRight (UniformScaling α) α := ⟨UniformScaling.val⟩

/-! ## Scalar instances (AT:345-348; port-notes §8.2 item 5)

Reals are their own scalar, even part and involution; their odd part is `0`
(Julia returns the `Int` `0` whatever the input type, bug B3; here it is `0`
in the input type). Julia defines none of these for `Complex`; the port
extends them to complex numbers in the same way. They are stated for every
`Coeff` type at low priority, so tensor types that later become coefficients
(DESIGN §4.1) keep their own, more specific instances. -/

section ScalarInstances

variable {α : Type}

instance (priority := low) [Coeff α] : GradeProj α 0 α := ⟨id⟩
instance (priority := low) [Coeff α] : Even α α := ⟨id⟩
instance (priority := low) [Coeff α] : Odd α α := ⟨fun _ => Coeff.zero⟩
instance (priority := low) [Coeff α] : Involute α := ⟨id⟩
/-- Julia `wedgedot(a, b) = a*b` on scalars (AT:350). -/
instance (priority := low) [Coeff α] : WedgeDot α α α := ⟨(· * ·)⟩
/-- Julia `contraction(a, b) = dot(a, b) = conj(a)*b` on scalars (AT:351). -/
instance (priority := low) [Coeff α] [Conj α] : Contraction α α α := ⟨fun a b => conj a * b⟩

end ScalarInstances

/-! ## Notation (DESIGN §4.4, scoped: `open AbstractTensors`) -/

/-- Exterior product; overloads `And` (35, right-assoc) through a choice node. -/
scoped infixr:35 " ∧ " => Wedge.wedge
/-- Regressive product; overloads `Or` (30, right-assoc) through a choice node. -/
scoped infixr:30 " ∨ " => Vee.vee
/-- Cross product; overloads `Prod` (35, right-assoc) through a choice node. -/
scoped infixr:35 " × " => Cross.cross
/-- Geometric product at `+` precedence (Julia `⊖`). -/
scoped infixl:65 " ⊖ " => WedgeDot.wedgedot
/-- Geometric product (Julia `⟑`, precedence of `*`); declared after `⊖` so
that terms print with `⟑`. -/
scoped infixl:70 " ⟑ " => WedgeDot.wedgedot
/-- Anti-geometric product (Julia `⟇`, precedence of `+`). -/
scoped infixl:65 " ⟇ " => VeeDot.veedot
/-- Right contraction (Julia `⨽`, `>`, `|`). -/
scoped infixl:70 " ⨽ " => Contraction.contraction
/-- Right contraction (Julia `⋅`, `dot`); declared after `⨽` so that terms
print with `⋅`. -/
scoped infixl:70 " ⋅ " => Contraction.contraction
/-- Left contraction (Julia `⨼`, `<`). -/
scoped infixl:70 " ⨼ " => leftContraction
/-- Reverse-geometric product (Julia `∗`). -/
scoped infixl:70 " ∗ " => reverseProduct
/-- Scalar product (Julia `⊛`). -/
scoped infixl:70 " ⊛ " => scalarProduct
/-- Sandwich (Julia `⊘`). -/
scoped infixl:70 " ⊘ " => Sandwich.sandwich
/-- Tensor product (Julia `⊗`). -/
scoped infixl:70 " ⊗ " => TensorProd.tensorProd
/-- Symmetrized product (Julia `⊙`). -/
scoped infixl:70 " ⊙ " => SymProd.symProd
/-- Antisymmetrized product (Julia `⊠`). -/
scoped infixl:70 " ⊠ " => AntiSymProd.antiSymProd
/-- Hodge complement (Julia prefix `⋆`); binds tighter than every binary operator. -/
scoped prefix:max "⋆" => Hodge.hodge
/-- Right complement (Julia `!`); overloads `not`, with the same operand
precedence (40), so the choice node picks by type. -/
scoped notation:max "!" t:40 => ComplementRight.complementRight t
/-- Reverse (Julia prefix `~`). -/
scoped prefix:max "~" => Reverse.reverse
/-- Even part (Julia postfix `₊`). -/
scoped postfix:max "₊" => Even.even
/-- Odd part (Julia postfix `₋`). -/
scoped postfix:max "₋" => Odd.odd
/-- Conjugate (Julia postfix `ǂ`). -/
scoped postfix:max "ǂ" => StaticVectors.Conj.conj
/-- Grade involution (Julia postfix `ˣ`). -/
scoped postfix:max "ˣ" => Involute.involute

end AbstractTensors
