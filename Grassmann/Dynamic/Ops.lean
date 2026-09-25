/-
The operator vocabulary on the dynamic layer: every AbstractTensors/Grassmann operator on
`TA V α` with Julia's result kinds, coercions into `TA`, numeric literals, and Julia's
predicates (Grassmann.jl `src/algebra.jl:285-401`, `src/multivectors.jl:1100-1150`;
AbstractTensors `src/AbstractTensors.jl:37-117, 183-240, 257-349, 425-480`).

After `open Grassmann`, Julia code such as `v1∧v2`, `~R*v1*R`, `x⊘R`, `R>>>x`, `⋆a`,
`!a`, `a×b`, `a₊`, `1 + v12` or `a ∥ 2a` can be written on dynamic elements and gives
Julia's result *kinds* and printed strings (the static layer gives the smallest static
container instead, DESIGN.md §4.2):

| Julia | Lean on `TA V α` | computed by |
|---|---|---|
| `a*b`, `a⟑b`, `a⊖b` | `a * b`, `a ⟑ b`, `a ⊖ b` | `TA.mul` |
| `a∧b`, `a∨b` | `a ∧ b`, `a ∨ b` (parenthesize: precedence 35/30) | `TA.wedge`, `TA.vee` |
| `a⋅b`, `a⨽b`, `a|b`, `a>b`; `a⨼b`, `a<b` | `a ⋅ b`, `a ⨽ b`; `a ⨼ b` | `TA.contraction` |
| `a<<b`, `a>>b` | `a ≪ b`, `a ≫ b` (`TA.lshift`, `TA.rshift`) | `contraction(b,~a)`, `contraction(~a,b)` |
| `a∗b`, `a⊛b`, `a×b`, `a⟇b`, `antidot(a,b)` | `a ∗ b`, `a ⊛ b`, `a × b`, `a ⟇ b`, `expansion a b` | `TA.revmul`, … |
| `x⊘R`, `R>>>x` | `x ⊘ R`, `R >>> x` | `TA.sandwich`, `TA.tsandwich` |
| `a⊙b`, `a⊠b` | `a ⊙ b`, `a ⊠ b` | `(ab ± ba)/2` |
| `⋆a`, `!a`, `complementleft(a)` | `⋆a`, `!a`, `complementLeft a` | `TA.hodge`, … |
| `~a`, `involute`, `clifford`, `conj` (`aǂ`), `aˣ` | `~a`, `involute a`, `clifford a`, `aǂ`, `aˣ` | sign maps |
| `a₊`, `a₋`, `scalar`, `vector`, …, `volume` | `a₊`, `a₋`, `scalar a`, …, `volume a` | parts |
| `a ∥ b` | `a ∥ b` | `iszero(a∧b)` |

Mixed operands convert through `IntoTA` (a static element, a basis blade `Submanifold`), so
`(x : TA V α) ∧ v₂` and `v₁ ⊘ (R : TA V α)` work; `CoeDep (Submanifold V G) b (TA V α)` lets the
`+ - *` elaborator lift a basis blade next to a dynamic operand. Numeric literals are
dynamic scalars: `(0 : TA V α)` is `𝟎` (Julia's `x + 0 = x`), any other `n` is the scalar
term `n·One(V)` (a `Single`, Julia's `x + n = x + n·One(V)`); an explicitly typed scalar
`s : α` uses Julia's number methods (`x + s`, `s * x`: `TA.addNum`, `TA.smul`).

Predicates (`src/multivectors.jl:1140-1144`, AbstractTensors `src/AbstractTensors.jl:37-117,
183-206, 444`): `istensor`, `isgraded` (terms and chains, including `𝟎` and `∞`), `isterm`,
`isscalar`/`isvector`/`isbivector`/`istrivector`/`isvolume` (for graded elements
`rank(t) == k || iszero(t)`, otherwise `norm(t) ≈ norm(part(t))`), `iszero`, `isone`
(`norm(t) ≈ value(scalar(t)) ≈ 1`), `isfinite`, `isapprox`. Julia's `iszero`/`isone` of a
basis blade throw (`UndefVarError(:V)` in `norm(::Submanifold)`); here a unit blade has
norm `1`.
-/
import Grassmann.Dynamic.Equal
import Grassmann.Notation

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

/-- Element types that embed into the dynamic layer of `V` with coefficients `α`: the
dynamic elements themselves, the static containers and terms, and the basis blades (a
`Submanifold` has no coefficient type of its own; it embeds at every `α`). -/
class IntoTA (X : Type) (V : TensorBundle) (α : Type) [Coeff α] where
  /-- The dynamic element (Julia's value of the same type). -/
  into : X → TA V α

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α]

instance : IntoTA (TA V α) V α := ⟨id⟩
instance {G : Nat} : IntoTA (Chain V G α) V α := ⟨ofChain⟩
instance {p : Bool} : IntoTA (Half V p α) V α := ⟨ofHalf⟩
instance : IntoTA (Multivector V α) V α := ⟨multi⟩
instance {G : Nat} : IntoTA (Single V G α) V α := ⟨ofSingle⟩
instance : IntoTA (Couple V α) V α := ⟨ofCouple⟩
instance : IntoTA (PseudoCouple V α) V α := ⟨ofPseudoCouple⟩
instance {G : Nat} : IntoTA (Submanifold V G) V α := ⟨fun b => ofBlade b.bits⟩

/-- A basis blade as a dynamic element: Julia's `Submanifold` value itself (`One` for the
scalar blade), at any coefficient type. -/
@[inline] def ofSubmanifold {G : Nat} (b : Submanifold V G) : TA V α := ofBlade b.bits

instance {G : Nat} (b : Submanifold V G) : CoeDep (Submanifold V G) b (TA V α) := ⟨ofSubmanifold b⟩

/-! ## Literals -/

/-- Julia numbers in sums and products: `0` is `𝟎`, any other `n` the scalar term
`n·One(V)` (see the module docstring). -/
instance {n : Nat} : OfNat (TA V α) n := ⟨if n == 0 then zero else single 0 (Coeff.ofInt n)⟩

/-- Decimal literals as scalar terms (`0.0` is `𝟎`, like the integer `0`). -/
instance [OfScientific α] : OfScientific (TA V α) where
  ofScientific m s e :=
    let x : α := OfScientific.ofScientific m s e
    if Coeff.isZero x then zero else single 0 x

instance : HAdd (TA V α) α (TA V α) := ⟨addNum⟩
instance : HAdd α (TA V α) (TA V α) := ⟨numAdd⟩
instance : HSub (TA V α) α (TA V α) := ⟨subNum⟩
instance : HSub α (TA V α) (TA V α) := ⟨numSub⟩

/-! ## Unary maps (AbstractTensors classes) -/

section Unary

variable [Kernels V]

instance : Reverse (TA V α) := ⟨reverse⟩
instance : Involute (TA V α) := ⟨involute⟩
instance : Clifford (TA V α) := ⟨clifford⟩
/-- Julia `conj(t)` (postfix `ǂ`): the reverse on tensors with real coefficients. -/
instance : Conj (TA V α) := ⟨reverse⟩
instance : Hodge (TA V α) (TA V α) := ⟨hodge⟩
instance : ComplementRight (TA V α) (TA V α) := ⟨complementright⟩
instance : ComplementLeft (TA V α) (TA V α) := ⟨complementleft⟩
instance : Even (TA V α) (TA V α) := ⟨even⟩
instance : Odd (TA V α) (TA V α) := ⟨odd⟩
instance : Volume (TA V α) (TA V α) := ⟨volume⟩

/-- Julia `scalar`, `vector`, `bivector`, `trivector` (grades `0…3`) and the grade-`G` part
beyond. -/
def part (G : Nat) (x : TA V α) : TA V α :=
  if G == 0 then scalar x else if G ≤ 3 then partProj G x else gradeProj G x

instance {G : Nat} : GradeProj (TA V α) G (TA V α) := ⟨part G⟩

/-- Julia `complementrightanti(t) = complementright(antimetric(t))`
(Grassmann `src/products.jl:1340-1345`). -/
@[inline] def complementrightanti (x : TA V α) : TA V α := complementright (antimetric x)

/-- Julia `complementleftanti(t) = complementleft(antimetric(t))`. -/
@[inline] def complementleftanti (x : TA V α) : TA V α := complementleft (antimetric x)

/-- Julia `pseudoreverse` (= `antireverse`). -/
@[inline] def pseudoreverse (x : TA V α) : TA V α := antireverse x

/-- Julia `cometric` / `pseudometric` of one element (= `antimetric`). -/
@[inline] def cometric (x : TA V α) : TA V α := antimetric x

end Unary

/-! ## Binary products (AbstractTensors classes) -/

section Binary

variable [Kernels V] {X : Type}

instance : WedgeDot (TA V α) (TA V α) (TA V α) := ⟨mul⟩
instance : Wedge (TA V α) (TA V α) (TA V α) := ⟨wedge⟩
instance : Vee (TA V α) (TA V α) (TA V α) := ⟨vee⟩
instance : Contraction (TA V α) (TA V α) (TA V α) := ⟨contraction⟩
instance : VeeDot (TA V α) (TA V α) (TA V α) := ⟨veedot⟩
instance : Expansion (TA V α) (TA V α) (TA V α) := ⟨antidot⟩
instance : Cross (TA V α) (TA V α) (TA V α) := ⟨cross⟩
instance : Sandwich (TA V α) (TA V α) (TA V α) := ⟨sandwich⟩
/-- Julia `R >>> x = R ⟑ x ⟑ clifford(R)`. -/
instance : HShiftRight (TA V α) (TA V α) (TA V α) := ⟨tsandwich⟩

/-- A static element or a basis blade next to a dynamic operand. -/
@[inline] def lift [IntoTA X V α] (x : X) : TA V α := IntoTA.into x

instance (priority := low) [IntoTA X V α] : HMul (TA V α) X (TA V α) := ⟨fun a b => mul a (lift b)⟩
instance (priority := low) [IntoTA X V α] : HMul X (TA V α) (TA V α) := ⟨fun a b => mul (lift a) b⟩
instance (priority := low) [IntoTA X V α] : WedgeDot (TA V α) X (TA V α) := ⟨fun a b => mul a (lift b)⟩
instance (priority := low) [IntoTA X V α] : WedgeDot X (TA V α) (TA V α) := ⟨fun a b => mul (lift a) b⟩
instance (priority := low) [IntoTA X V α] : Wedge (TA V α) X (TA V α) := ⟨fun a b => wedge a (lift b)⟩
instance (priority := low) [IntoTA X V α] : Wedge X (TA V α) (TA V α) := ⟨fun a b => wedge (lift a) b⟩
instance (priority := low) [IntoTA X V α] : Vee (TA V α) X (TA V α) := ⟨fun a b => vee a (lift b)⟩
instance (priority := low) [IntoTA X V α] : Vee X (TA V α) (TA V α) := ⟨fun a b => vee (lift a) b⟩
instance (priority := low) [IntoTA X V α] : Contraction (TA V α) X (TA V α) :=
  ⟨fun a b => contraction a (lift b)⟩
instance (priority := low) [IntoTA X V α] : Contraction X (TA V α) (TA V α) :=
  ⟨fun a b => contraction (lift a) b⟩
instance (priority := low) [IntoTA X V α] : Cross (TA V α) X (TA V α) := ⟨fun a b => cross a (lift b)⟩
instance (priority := low) [IntoTA X V α] : Cross X (TA V α) (TA V α) := ⟨fun a b => cross (lift a) b⟩
instance (priority := low) [IntoTA X V α] : Sandwich (TA V α) X (TA V α) :=
  ⟨fun a b => sandwich a (lift b)⟩
instance (priority := low) [IntoTA X V α] : Sandwich X (TA V α) (TA V α) :=
  ⟨fun a b => sandwich (lift a) b⟩
instance (priority := low) [IntoTA X V α] : HShiftRight (TA V α) X (TA V α) :=
  ⟨fun a b => tsandwich a (lift b)⟩
instance (priority := low) [IntoTA X V α] : HShiftRight X (TA V α) (TA V α) :=
  ⟨fun a b => tsandwich (lift a) b⟩

/-- Julia `⊙(a, b) = (a⟑b + b⟑a)/2`, the symmetrization projection (`src/algebra.jl:294`;
Julia's version needs `Combinatorics.permutations`, which Grassmann does not load: defect
`symmetrize-permutations`, the intended formula is implemented). -/
def symprod [Div α] (a b : TA V α) : TA V α := divScalar (mul a b + mul b a) (Coeff.ofInt 2)

/-- Julia `⊠(a, b) = (a⟑b - b⟑a)/2`, the anti-symmetrization projection
(`src/algebra.jl:301-309`; defect `symmetrize-permutations`). -/
def antisymprod [Div α] (a b : TA V α) : TA V α := divScalar (mul a b - mul b a) (Coeff.ofInt 2)

instance [Div α] : SymProd (TA V α) (TA V α) (TA V α) := ⟨symprod⟩
instance [Div α] : AntiSymProd (TA V α) (TA V α) (TA V α) := ⟨antisymprod⟩

/-- Julia `pseudosandwich(x, R) = cosandwich(x, R) = complementleft(sandwich(!x, !R))`
(AbstractTensors `src/AbstractTensors.jl:559`). -/
@[inline] def cosandwich (x R : TA V α) : TA V α :=
  complementleft (sandwich (complementright x) (complementright R))

/-- Julia `antisandwich(R, x) = complementleft(complementright(R) >>> complementright(x))`
(AbstractTensors `src/AbstractTensors.jl:568`; the versor comes first, as in `>>>`). -/
@[inline] def antisandwich (R x : TA V α) : TA V α :=
  complementleft (tsandwich (complementright R) (complementright x))

/-- Julia `codot` (= `antidot`, `expansion`). -/
@[inline] def codot (a b : TA V α) : TA V α := antidot a b

end Binary

/-! ## Predicates -/

section Predicates

/-- Julia `istensor(t)`: every dynamic element is a `TensorAlgebra`. -/
@[inline] def istensor (_ : TA V α) : Bool := true

/-- Julia `isterm(t)` (a `TensorTerm`: `𝟎`, `One`, `∞`, a basis blade, a `Single`). -/
def isterm : TA V α → Bool
  | zero | one | infinity | blade _ | single .. => true
  | _ => false

/-- Julia `isgraded(t)` (a `TensorGraded`: a term or a `Chain`). -/
def isgraded : TA V α → Bool
  | chain .. => true
  | x => isterm x

/-- Julia `rank(t)`/`grade(t)` of a graded element (`none` for mixed kinds). -/
@[inline] def rank? (x : TA V α) : Option Nat := x.grade?

variable [Kernels V] [JNorm α]

/-- Julia `iszero(t) = norm(t) ≈ 0` (i.e. `norm(t) == 0`; `∞` is not zero). -/
def iszero (x : TA V α) : Bool := norm x == 0

/-- `rank(t) == k || iszero(t)` for a graded element, `norm(t) ≈ norm(part(t))` otherwise
(AbstractTensors `src/AbstractTensors.jl:192-206`, Grassmann `src/multivectors.jl:1140-1144`). -/
def isPart (k : Nat) (part : TA V α → TA V α) (x : TA V α) : Bool :=
  match x.grade? with
  | some g => g == k || iszero x
  | none => F64.isapprox (norm x) (norm (part x))

/-- Julia `isvector(t)`. -/
def isvector (x : TA V α) : Bool := isPart 1 vector x
/-- Julia `isbivector(t)`. -/
def isbivector (x : TA V α) : Bool := isPart 2 bivector x
/-- Julia `istrivector(t)`. -/
def istrivector (x : TA V α) : Bool := isPart 3 trivector x

/-- Julia `isvolume(t)`: `rank(t) == mdims(t) || iszero(t)` for a graded element, else
`norm(t) ≈ norm(volume(t))`. -/
def isvolume (x : TA V α) : Bool :=
  match x.grade? with
  | some g => g == V.n || iszero x
  | none => F64.isapprox (norm x) (norm (volume x))

/-- Julia `isone(t) = norm(t) ≈ value(scalar(t)) ≈ 1` (AbstractTensors
`src/AbstractTensors.jl:444`), with `α`'s default tolerance for the last comparison. -/
def isone [JApprox α] (x : TA V α) : Bool :=
  let s := (scalar x).coeff 0
  JApprox.isapprox s Coeff.one 0 (JApprox.rtolDefault (α := α)) false &&
    F64.isapprox (norm x) (JNorm.norm s)

/-- Julia `isfinite(t)`: every coefficient is finite (Julia defines it for terms,
`isfinite(value(t))`, AbstractTensors `src/AbstractTensors.jl:117`; containers extend it
coefficientwise). `∞` is not finite. -/
def isfinite (x : TA V α) : Bool :=
  match x with
  | infinity => false
  | phasor amp θ => (JNorm.norm amp).isFinite && (norm θ).isFinite
  | _ => x.toDense.v.all fun c => (JNorm.norm c).isFinite

/-- Julia `a ∥ b = iszero(a ∧ b)` (`src/algebra.jl:401`): whether two elements are
parallel. -/
def parallel (a b : TA V α) : Bool := iszero (wedge a b)

instance : Parallel (TA V α) (TA V α) := ⟨parallel⟩

/-- Julia `isapprox(a, b; atol, rtol)` (AbstractTensors `src/AbstractTensors.jl:229-240`,
Grassmann `src/multivectors.jl:1103-1105`): two chains of one grade and two containers of
one kind compare coefficientwise; two graded elements of different grades are
approximately equal only when both are zero; otherwise finite norms and
`norm(a - b) ≤ max(atol, rtol·max(norm a, norm b))`, with `rtol = rtoldefault(α)`
(`√eps` for floats, `0` for exact types) unless `atol > 0`. -/
def isapprox [JApprox α] (a b : TA V α) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else JApprox.rtolDefault (α := α)) : Bool :=
  let cw := fun (x y : TA V α) =>
    Values.foldl₂ (fun acc c d => acc && JApprox.isapprox c d atol rtol false) true
      x.toDense.v y.toDense.v
  let normRule := fun (_ : Unit) =>
    let x := norm a
    let y := norm b
    x.isFinite && y.isFinite && norm (a - b) ≤ F64.max atol (rtol * F64.max x y)
  match a, b with
  | chain g _, chain h _ => if g == h then cw a b else iszero a && iszero b
  | multi _, multi _ | spinor _, spinor _ | cospinor _, cospinor _ => cw a b
  | _, _ => match a.grade?, b.grade? with
    | some g, some h => if g == h then normRule () else iszero a && iszero b
    | _, _ => normRule ()

end Predicates

end TA

end Grassmann
