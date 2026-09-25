import Tests.Golden.Registry
import Grassmann.Dynamic

/-!
# Oracle bridge for the dynamic layer (`Grassmann.TA`)

Decoding of oracle element objects (docs/port-notes/oracle-schema.md §7) into
`Grassmann.TA V α` for every coefficient type the goldens use, and encoding of
dynamic results back into `GoldenElem`s with Julia's *kind*, `grade`/`bits`, `T`,
dense values and printed strings (`str`, `compact_str`).

| Julia `T` | Lean coefficient |
|---|---|
| `Int64` | `Int` |
| `Rational{Int64}` | `Rat` |
| `Float64` | `Float` |
| `Bool` | `JBool` (display only; Julia promotes `Bool` sums to `Int`) |
| `Complex{Int64}`, `Complex{Rational{Int64}}`, `Complex{Float64}` | `JuliaBase.Complex α` |

`AnyTA V` carries one of these; binary operations promote both operands to Julia's
`promote_type` of their coefficient types first (`Int64 + Float64 → Float64`). The
`T` of a result is that promoted type, except for Julia's typeless kinds: `Zero`,
`One` and basis blades are `Int64`, `Infinity` is `Float64`.

The evaluators themselves live in `Tests.Golden.GrassmannEval`.
-/

namespace Tests.ElementOracle.Dyn

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-! ## Julia `Bool` coefficients -/

/-- Julia `Bool` as a coefficient (display only: Julia promotes `true + true` to the
`Int` `2`; here the arithmetic is Boolean). A type synonym, so its instances do not
leak to `Bool`. -/
def JBool := Bool

instance : Inhabited JBool := ⟨(false : Bool)⟩

instance : Coeff JBool where
  add a b := (a || b : Bool)
  sub a b := (a && !b : Bool)
  mul a b := (a && b : Bool)
  neg a := a
  zero := (false : Bool)
  one := (true : Bool)
  ofInt k := (k != 0 : Bool)
  ofRat r := (r != 0 : Bool)
  isZero x := !(x : Bool)

instance : JuliaShow JBool := inferInstanceAs (JuliaShow Bool)

/-! ## Scalars -/

/-- A scalar coefficient type of the oracle as a Lean coefficient type. -/
class OracleScalar (α : Type) where
  /-- Decode an oracle scalar (`none` if it does not fit). -/
  ofScalar : Scalar → Option α
  /-- Encode a dense vector. -/
  toCoeffs : Array α → Coeffs
  /-- Julia's name of the type. -/
  T : CoeffType

instance : OracleScalar Int where
  ofScalar | .exact q => if q.den == 1 then some q.num else none | _ => none
  toCoeffs a := .exact (a.map Int.cast)
  T := .int64

instance : OracleScalar Rat where
  ofScalar | .exact q => some q | _ => none
  toCoeffs a := .exact a
  T := .rational

instance : OracleScalar Float where
  ofScalar | .float f => some f | _ => none
  toCoeffs a := .float (a.foldl (·.push ·) (FloatArray.emptyWithCapacity a.size))
  T := .float64

instance : OracleScalar JBool where
  ofScalar | .exact q => some (q != 0 : Bool) | _ => none
  toCoeffs a := .exact (a.map fun (x : Bool) => if x then 1 else 0)
  T := .bool

instance : OracleScalar (Complex Int) where
  ofScalar
    | .complex (.exact a) (.exact b) => if a.den == 1 && b.den == 1 then some ⟨a.num, b.num⟩ else none
    | _ => none
  toCoeffs a := .complexExact (a.map fun z => Int.cast z.re) (a.map fun z => Int.cast z.im)
  T := .complex .int64

instance : OracleScalar (Complex Rat) where
  ofScalar | .complex (.exact a) (.exact b) => some ⟨a, b⟩ | _ => none
  toCoeffs a := .complexExact (a.map (·.re)) (a.map (·.im))
  T := .complex .rational

instance : OracleScalar (Complex Float) where
  ofScalar | .complex (.float a) (.float b) => some ⟨a, b⟩ | _ => none
  toCoeffs a := .complexFloat (a.foldl (fun acc z => acc.push z.re) FloatArray.empty)
    (a.foldl (fun acc z => acc.push z.im) FloatArray.empty)
  T := .complex .float64

/-! ## Decoding elements -/

variable {V : TensorBundle}

/-- The coefficients of an element in its storage order: `native` when present
(construct), else gathered from `dense` at the kind's support (schema §7.1). -/
def storageValues {α : Type} [OracleScalar α] (n : Nat) (e : GoldenElem) : Option (Array α) := do
  let cs ← match e.native with
    | some nat => pure ((List.range nat.size).toArray.map nat.get)
    | none => do
      let d ← e.dense
      let supp ← supportIndices n e.kind (e.grade.getD 0) (e.bits.getD 0)
      pure (supp.map d.get)
  cs.mapM OracleScalar.ofScalar

/-- Decode an element object into a dynamic element of `V` with coefficients `α`
(`none` for Numbers, errors, elements of another space and undecodable values). -/
partial def decodeTA {α : Type} [Coeff α] [OracleScalar α] (V : TensorBundle) (e : GoldenElem) :
    Option (TA V α) := do
  if e.V.isSome then none
  match e.kind with
  | .zero => pure .zero
  | .one => pure .one
  | .infinity => pure .infinity
  | .submanifold => pure (.blade (← e.bits))
  | .phasor =>
    let a ← e.amp
    let amp ← OracleScalar.ofScalar ((← a.value).get 0)
    pure (.phasor amp (← decodeTA V (← e.angle)))
  | .single => pure (.single (← e.bits) (← (← storageValues V.n e)[0]?))
  | .couple => let v ← storageValues (α := α) V.n e; pure (.couple (← e.bits) (← v[0]?) (← v[1]?))
  | .pseudoCouple => let v ← storageValues (α := α) V.n e; pure (.pseudo (← e.bits) (← v[0]?) (← v[1]?))
  | .chain =>
    let g ← e.grade
    let c : Chain V g α ← Chain.ofArray? (← storageValues V.n e)
    pure (.chain g c)
  | .spinor => pure (.spinor (← Half.ofArray? (← storageValues V.n e)))
  | .cospinor => pure (.cospinor (← Half.ofArray? (← storageValues V.n e)))
  | .multivector => pure (.multi (← Multivector.ofArray? (← storageValues V.n e)))
  | _ => none

/-! ## Encoding results -/

/-- The oracle kind of a dynamic kind. -/
def kindOf : TA.Kind → Kind
  | .zero => .zero | .one => .one | .infinity => .infinity | .submanifold => .submanifold
  | .single => .single | .chain => .chain | .spinor => .spinor | .cospinor => .cospinor
  | .multivector => .multivector | .couple => .couple | .pseudoCouple => .pseudoCouple
  | .phasor => .phasor

/-- Julia's `valuetype` of a result computed with coefficient type `T`: typeless kinds
have their nominal type. -/
def resultT (k : TA.Kind) (T : CoeffType) : CoeffType :=
  match k with
  | .zero | .one | .submanifold => .int64
  | .infinity => .float64
  | _ => T

/-- Encode a dynamic element: kind, `T`, `grade`, `bits`, dense values and both
printed forms. -/
def encodeTA {α : Type} [Coeff α] [JuliaShow α] [OracleScalar α] (x : TA V α) : GoldenElem :=
  let k := x.kind
  let dense : Option Coeffs := if x.IsLinear then
      some (OracleScalar.toCoeffs x.toDense.v.toArray)
    else none
  { kind := kindOf k, T := some (resultT k (OracleScalar.T α)), grade := x.grade?, bits := x.bits?,
    dense, str := .val x.showString, compactStr := .val x.showCompact }

/-! ## Elements with any coefficient type -/

/-- A dynamic element with one of the oracle's coefficient types. -/
inductive AnyTA (V : TensorBundle) where
  /-- `Int64`. -/
  | int (x : TA V Int)
  /-- `Rational{Int64}`. -/
  | rat (x : TA V Rat)
  /-- `Float64`. -/
  | float (x : TA V Float)
  /-- `Bool`. -/
  | bool (x : TA V JBool)
  /-- `Complex{Int64}`. -/
  | cint (x : TA V (Complex Int))
  /-- `Complex{Rational{Int64}}`. -/
  | crat (x : TA V (Complex Rat))
  /-- `Complex{Float64}`. -/
  | cfloat (x : TA V (Complex Float))

namespace AnyTA

/-- Decode an element with its own coefficient type. -/
def decode (V : TensorBundle) (e : GoldenElem) : Option (AnyTA V) := do
  match ← e.T with
  | .int64 => .int <$> decodeTA V e
  | .rational => .rat <$> decodeTA V e
  | .float64 => .float <$> decodeTA V e
  | .bool => .bool <$> decodeTA V e
  | .complex .int64 => .cint <$> decodeTA V e
  | .complex .rational => .crat <$> decodeTA V e
  | .complex .float64 => .cfloat <$> decodeTA V e
  | _ => none

/-- The coefficient type. -/
def T : AnyTA V → CoeffType
  | int _ => .int64 | rat _ => .rational | float _ => .float64 | bool _ => .bool
  | cint _ => .complex .int64 | crat _ => .complex .rational | cfloat _ => .complex .float64

/-- Encode (see `encodeTA`). -/
def encode : AnyTA V → GoldenElem
  | int x => encodeTA x | rat x => encodeTA x | float x => encodeTA x | bool x => encodeTA x
  | cint x => encodeTA x | crat x => encodeTA x | cfloat x => encodeTA x

/-- `Int64 → Float64`. -/
def intToFloat (k : Int) : Float := Float.ofInt k

/-- Convert to coefficient type `T` (Julia's `promote`): `Bool ⊂ Int64 ⊂ Rational ⊂ Float64`,
and their complex versions. `none` for a demotion. -/
def promoteTo (T : CoeffType) (x : AnyTA V) : Option (AnyTA V) :=
  match T, x with
  | .int64, int x => some (int x)
  | .int64, bool x => some (int (x.map fun (b : JBool) => cond (show Bool from b) 1 0))
  | .rational, int x => some (rat (x.map Int.cast))
  | .rational, rat x => some (rat x)
  | .float64, int x => some (float (x.map intToFloat))
  | .float64, rat x => some (float (x.map JuliaBase.F64.ofRat))
  | .float64, float x => some (float x)
  | .complex .int64, int x => some (cint (x.map fun k => ⟨k, 0⟩))
  | .complex .int64, cint x => some (cint x)
  | .complex .float64, int x => some (cfloat (x.map fun k => ⟨intToFloat k, 0⟩))
  | .complex .float64, float x => some (cfloat (x.map fun f => ⟨f, 0⟩))
  | .complex .float64, cfloat x => some (cfloat x)
  | .complex .rational, crat x => some (crat x)
  | _, _ => none

end AnyTA

/-! ## Numbers -/

/-- A number operand (arith inputs `n:2`, `n:0`, `n:0.5`). -/
inductive AnyNum where
  /-- An `Int64`. -/
  | int (k : Int)
  /-- A `Float64`. -/
  | float (f : Float)
  /-- A `Rational{Int64}`. -/
  | rat (q : Rat)

namespace AnyNum

/-- Decode a Number element. -/
def decode (e : GoldenElem) : Option AnyNum := do
  if e.kind != .number then none
  match ← e.T, (← e.value).get 0 with
  | .int64, .exact q => if q.den == 1 then some (int q.num) else none
  | .rational, .exact q => some (rat q)
  | .float64, .float f => some (float f)
  | _, _ => none

/-- The coefficient type. -/
def T : AnyNum → CoeffType
  | int _ => .int64 | float _ => .float64 | rat _ => .rational

/-- Whether it is zero (Julia `iszero`). -/
def isZero : AnyNum → Bool
  | int k => k == 0 | float f => f == 0 | rat q => q == 0

end AnyNum

/-- An operand: an element or a number. -/
inductive DynOperand (V : TensorBundle) where
  /-- An algebra element. -/
  | elem (x : AnyTA V)
  /-- A plain number. -/
  | num (n : AnyNum)

/-- Decode an operand. -/
def DynOperand.decode (V : TensorBundle) (e : GoldenElem) : Option (DynOperand V) :=
  if e.kind == .number then .num <$> AnyNum.decode e else .elem <$> AnyTA.decode V e

/-- The coefficient type of an operand. -/
def DynOperand.T : DynOperand V → CoeffType
  | .elem x => x.T
  | .num n => n.T

/-! ## Operations at a common coefficient type -/

/-- A binary operation on dynamic elements, polymorphic in the coefficient type. -/
abbrev BinTA (V : TensorBundle) :=
  {α : Type} → [Coeff α] → [JuliaShow α] → [OracleScalar α] → TA V α → TA V α → TA V α

/-- A unary operation on dynamic elements, polymorphic in the coefficient type. -/
abbrev UnTA (V : TensorBundle) :=
  {α : Type} → [Coeff α] → [JuliaShow α] → [OracleScalar α] → TA V α → TA V α

/-- Apply a binary operation after promoting both operands to type `T`. -/
def AnyTA.bin (T : CoeffType) (f : BinTA V) (a b : AnyTA V) : Option (AnyTA V) := do
  match ← a.promoteTo T, ← b.promoteTo T with
  | .int x, .int y => pure (.int (f x y))
  | .rat x, .rat y => pure (.rat (f x y))
  | .float x, .float y => pure (.float (f x y))
  | .cint x, .cint y => pure (.cint (f x y))
  | .crat x, .crat y => pure (.crat (f x y))
  | .cfloat x, .cfloat y => pure (.cfloat (f x y))
  | _, _ => none

/-- Apply a unary operation. -/
def AnyTA.un (f : UnTA V) : AnyTA V → AnyTA V
  | .int x => .int (f x) | .rat x => .rat (f x) | .float x => .float (f x) | .bool x => .bool (f x)
  | .cint x => .cint (f x) | .crat x => .crat (f x) | .cfloat x => .cfloat (f x)

/-- An operation on several dynamic elements of one coefficient type. -/
abbrev NaryTA (V : TensorBundle) :=
  {α : Type} → [Coeff α] → [JuliaShow α] → [OracleScalar α] → Array (TA V α) → TA V α

/-- Apply an operation on several elements after promoting them all to type `T`. -/
def AnyTA.nary (T : CoeffType) (f : NaryTA V) (xs : Array (AnyTA V)) : Option (AnyTA V) := do
  let ys ← xs.mapM (·.promoteTo T)
  match T with
  | .int64 => .int <$> (f <$> ys.mapM fun | .int x => some x | _ => none)
  | .rational => .rat <$> (f <$> ys.mapM fun | .rat x => some x | _ => none)
  | .float64 => .float <$> (f <$> ys.mapM fun | .float x => some x | _ => none)
  | .complex .int64 => .cint <$> (f <$> ys.mapM fun | .cint x => some x | _ => none)
  | .complex .rational => .crat <$> (f <$> ys.mapM fun | .crat x => some x | _ => none)
  | .complex .float64 => .cfloat <$> (f <$> ys.mapM fun | .cfloat x => some x | _ => none)
  | _ => none

/-- The blade of a term, `Couple` or `PseudoCouple`. -/
def AnyTA.blade? (x : AnyTA V) : Option UInt64 :=
  let f := fun {α : Type} [Coeff α] (t : TA V α) => match t with
    | .blade b | .single b _ | .couple b .. | .pseudo b .. => some b
    | .one => some 0
    | _ => none
  match x with
  | .int t => f t | .rat t => f t | .float t => f t | .bool t => f t
  | .cint t => f t | .crat t => f t | .cfloat t => f t

/-- The `Float64` version of the coefficient type (`Complex{Float64}` for complex types). -/
def AnyTA.toFloat (x : AnyTA V) : Option (AnyTA V) :=
  match x with
  | .bool _ => (x.promoteTo .int64).bind (·.promoteTo .float64)
  | .cint _ | .crat _ | .cfloat _ => x.promoteTo (.complex .float64)
  | _ => x.promoteTo .float64

/-- Julia's term `complementright`/`complementleft` in a conformal space scales a blade
holding `∅` but not `∞` by `v/2` (Leibniz `src/generic.jl:214-219`, `parityrightnull`),
so an integer or rational coefficient comes back `Float64`; `Couple`/`PseudoCouple`
complements go through their `B` term. Apply the complement `f` with that promotion. -/
def AnyTA.complement (f : UnTA V) (x : AnyTA V) : AnyTA V :=
  let halves := V.hasconformal && match x.blade? with
    | some b => DirectSum.Bits.popcount (b &&& 3) == 1 && b &&& 1 == 0
    | none => false
  if halves then ((x.toFloat).getD x).un f else x.un f

/-- A number as a dynamic scalar term `n·One(V)` (Julia `n*One(V)`, a `Single`). -/
def AnyNum.toTA (V : TensorBundle) : AnyNum → AnyTA V
  | .int k => .int (.single 0 k)
  | .float f => .float (.single 0 f)
  | .rat q => .rat (.single 0 q)

end Tests.ElementOracle.Dyn
