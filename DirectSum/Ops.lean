/-
The blade-level interface the Grassmann core consumes (DESIGN.md §3, §5.1-5.3).

Everything a product kernel needs from DirectSum, in one place:

* **Operations** as data: `BinOp` (`*`, `∧`, `∨`, `⋅`, `⨼`, `<<`, `>>`, `∗`,
  `⊛`, `×`, `⟇`, `antidot`) and `UnOp` (involutions, complements, metric,
  grade projections), evaluated by `TensorBundle.apply₂`/`apply₁` to Julia's
  result kinds (`BladeResult`), or by `terms₂`/`terms₁` to plain `Rat`
  coefficient lists (`BladeTerm`).
* **Container layouts** (`Layout`): a grade-`G` `Chain`, the even/odd halves
  (`Spinor`/`CoSpinor`) and the full `Multivector`, with Julia's storage order
  (`Leibniz.indexBasis`, `spinRank`, `antiRank`, `basisRank`).
* **Plans** (`plan₂`, `plan₁`): the sparse multiply-accumulate lists
  `out[ic] += coef · x[ia] · y[ib]` of an operation between two layouts,
  built from the blade rules. Code generation emits them as straight-line
  code; fallback kernels interpret them (DESIGN §5.2-5.3).
* **Typed blades**: `Submanifold V G` gets the AbstractTensors kind classes
  (`TensorTerm … V G Int`, as Julia's `Submanifold{V,G,B} <: TensorTerm{V,G,Int}`)
  and typed wrappers of the operations.

Tangent spaces: a repeated `∂` makes a coefficient the blade `e_z` of
`V.loworder` (Julia's nested `Single`, grassmann-parity.md §4.11); such terms
carry `z ≠ 0` and every other term has `z = 0`.
-/
import DirectSum.Derived
import DirectSum.Blade
import DirectSum.Names
import AbstractTensors.Ops

namespace DirectSum

open Bits Leibniz

/-! ## Operations as data -/

/-- A binary blade-level operation; the Julia spellings are in the docstrings. -/
inductive BinOp where
  /-- Geometric product `a * b`, `a ⟑ b`, `wedgedot` (`TensorBundle.mul`). -/
  | mul
  /-- Exterior product `a ∧ b` (`TensorBundle.wedge`). -/
  | wedge
  /-- Regressive product `a ∨ b`, `a & b` (`TensorBundle.vee`). -/
  | vee
  /-- `contraction(a,b)`, `a ⋅ b`, `a ⨽ b`, `a > b`, `a | b`, `dot` (`TensorBundle.contraction`). -/
  | contraction
  /-- `a ⨼ b`, `a < b` = `contraction(b,a)`. -/
  | contractionLeft
  /-- `a << b` = `contraction(b,~a)`. -/
  | contractionRevLeft
  /-- `a >> b` = `contraction(~a,b)`. -/
  | contractionRevRight
  /-- `a ∗ b` = `(~a) ⟑ b`. -/
  | reverseMul
  /-- `a ⊛ b` = `scalar(contraction(a,b))`. -/
  | scalarContraction
  /-- `cross(a,b)`, `a × b` = `⋆(a ∧ b)`. -/
  | cross
  /-- `veedot(a,b)`, `a ⟇ b` = `complementleft(!a * !b)`. -/
  | veedot
  /-- `antidot(a,b)` = `complementleft(contraction(!a,!b))`. -/
  | antidot
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Every binary operation. -/
def BinOp.all : List BinOp :=
  [.mul, .wedge, .vee, .contraction, .contractionLeft, .contractionRevLeft, .contractionRevRight,
   .reverseMul, .scalarContraction, .cross, .veedot, .antidot]

/-- A unary blade-level operation. -/
inductive UnOp where
  /-- `~b`, `reverse(b)`. -/
  | reverse
  /-- `involute(b)`. -/
  | involute
  /-- `clifford(b)` = involute ∘ reverse. -/
  | clifford
  /-- `conj(b)` (= reverse on real blades). -/
  | conj
  /-- `antireverse(b)`, `pseudoreverse(b)`. -/
  | antireverse
  /-- `pseudoinvolute(b)`. -/
  | antiinvolute
  /-- `pseudoclifford(b)`. -/
  | anticlifford
  /-- `!b`, `complementright(b)` (Euclidean; conformal null scaling `2`/`½`). -/
  | complementright
  /-- `complementleft(b)`. -/
  | complementleft
  /-- `⋆b`, `hodge(b)`, `complementrighthodge(b)`. -/
  | complementrighthodge
  /-- `complementlefthodge(b)`. -/
  | complementlefthodge
  /-- `metric(b)`. -/
  | metric
  /-- `antimetric(b)`. -/
  | antimetric
  /-- `complementrightanti(b)`. -/
  | complementrightanti
  /-- `complementleftanti(b)`. -/
  | complementleftanti
  /-- `even(b)`. -/
  | even
  /-- `odd(b)`. -/
  | odd
  /-- `real(b)`. -/
  | real
  /-- `imag(b)`. -/
  | imag
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Every unary operation. -/
def UnOp.all : List UnOp :=
  [.reverse, .involute, .clifford, .conj, .antireverse, .antiinvolute, .anticlifford,
   .complementright, .complementleft, .complementrighthodge, .complementlefthodge, .metric,
   .antimetric, .complementrightanti, .complementleftanti, .even, .odd, .real, .imag]

/-- One term `coef · e_bits` of a blade-level result, additionally multiplied
by the blade `e_z` of `V.loworder` when `z ≠ 0` (a repeated tangent `∂`). -/
structure BladeTerm where
  /-- The blade mask (bit `k-1` ⇔ generator `k`). -/
  bits : UInt64
  /-- The exact coefficient. -/
  coef : Rat
  /-- Repeated tangent bits (0 unless the space is tangent). -/
  z : UInt64 := 0
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace BladeResult

/-- The terms of a result as `BladeTerm`s (nonzero coefficients only; a `0v`
`Single` of a degenerate metric gives no term). -/
def bladeTerms : BladeResult → Array BladeTerm
  | nested z r => r.bladeTerms.map fun t => { t with z := z ||| t.z }
  | r => (r.terms.filter (·.2 != 0)).map fun (b, c) => { bits := b, coef := c }

end BladeResult

namespace TensorBundle

variable (V : TensorBundle)

/-- Evaluate a binary operation on two basis blades, with Julia's result kind.
Errors are Julia's (complements in a dyadic space). -/
def apply₂ : BinOp → UInt64 → UInt64 → Except String BladeResult
  | .mul, a, b => .ok (V.mul a b)
  | .wedge, a, b => .ok (V.wedge a b)
  | .vee, a, b => .ok (V.vee a b)
  | .contraction, a, b => .ok (V.contraction a b)
  | .contractionLeft, a, b => .ok (V.contractionLeft a b)
  | .contractionRevLeft, a, b => V.contractionRevLeft a b
  | .contractionRevRight, a, b => V.contractionRevRight a b
  | .reverseMul, a, b => V.reverseMul a b
  | .scalarContraction, a, b => .ok (V.scalarContraction a b)
  | .cross, a, b => V.cross a b
  | .veedot, a, b => V.veedot a b
  | .antidot, a, b => V.antidot a b

/-- Evaluate a unary operation on a basis blade, with Julia's result kind. -/
def apply₁ : UnOp → UInt64 → Except String BladeResult
  | .reverse, b => .ok (V.reverse b)
  | .involute, b => .ok (V.involute b)
  | .clifford, b => .ok (V.clifford b)
  | .conj, b => .ok (V.conj b)
  | .antireverse, b => .ok (V.antireverse b)
  | .antiinvolute, b => .ok (V.antiinvolute b)
  | .anticlifford, b => .ok (V.anticlifford b)
  | .complementright, b => V.complementright b
  | .complementleft, b => V.complementleft b
  | .complementrighthodge, b => V.complementrighthodge b
  | .complementlefthodge, b => V.complementlefthodge b
  | .metric, b => V.bladeMetric b
  | .antimetric, b => V.antimetric b
  | .complementrightanti, b => V.complementrightanti b
  | .complementleftanti, b => V.complementleftanti b
  | .even, b => .ok (evenPart b)
  | .odd, b => .ok (oddPart b)
  | .real, b => .ok (realPart b)
  | .imag, b => .ok (imagPart b)

/-- `op a b` as exact `Rat` terms (merged, zeros dropped, basis order). -/
def terms₂ (op : BinOp) (a b : UInt64) : Except String (Array BladeTerm) :=
  return (← V.apply₂ op a b).bladeTerms

/-- `op b` as exact `Rat` terms. -/
def terms₁ (op : UnOp) (b : UInt64) : Except String (Array BladeTerm) :=
  return (← V.apply₁ op b).bladeTerms

end TensorBundle

/-! ## Container layouts and product plans -/

/-- A coefficient container's storage layout (DESIGN.md §4.2). -/
inductive Layout where
  /-- `Chain V G`: the grade-`G` blades in lex order (Julia `indexbasis(n,G)`). -/
  | chain (g : Nat)
  /-- `Spinor V`: the even-grade blades, grade-major (Julia `spinindex`). -/
  | even
  /-- `CoSpinor V`: the odd-grade blades, grade-major (Julia `antiindex`). -/
  | odd
  /-- `Multivector V`: all `2ⁿ` blades, grade-major (Julia `basisindex`). -/
  | full
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Layout

/-- Number of stored coefficients in an `n`-generator space. -/
def size (n : Nat) : Layout → Nat
  | chain g => choose n g
  | even => if n == 0 then 1 else 2 ^ (n - 1)
  | odd => if n == 0 then 0 else 2 ^ (n - 1)
  | full => 2 ^ n

/-- The blades in storage order. -/
def blades (n : Nat) : Layout → Array UInt64
  | chain g => indexBasis n g
  | even => indexEven n
  | odd => indexOdd n
  | full => indexBasisAll n

/-- Whether blade `b` is stored in the layout. -/
def contains (n : Nat) (l : Layout) (b : UInt64) : Bool :=
  b &&& ~~~(lowMask n) == 0 &&
    match l with
    | chain g => popcount b == g
    | even => popcount b % 2 == 0
    | odd => popcount b % 2 == 1
    | full => true

/-- 0-based storage position of a blade the layout contains. -/
def rank (n : Nat) : Layout → UInt64 → Nat
  | chain _, b => bladeRank n b
  | even, b => spinRank n b
  | odd, b => antiRank n b
  | full, b => basisRank n b

end Layout

/-- One multiply-accumulate step `out[ic] += coef · x[ia] · y[ib]` of a binary
kernel (times the tangent blade `e_z` of `V.loworder` when `z ≠ 0`); unary
plans leave `ib = 0`. Positions are 0-based storage positions. -/
structure PlanEntry where
  /-- Position in the first operand. -/
  ia : Nat
  /-- Position in the second operand (0 for unary plans). -/
  ib : Nat
  /-- Position in the result. -/
  ic : Nat
  /-- Exact coefficient. -/
  coef : Rat
  /-- Repeated tangent bits (0 unless the space is tangent). -/
  z : UInt64 := 0
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace TensorBundle

variable (V : TensorBundle)

/-- Place blade-level terms into the result layout, failing if a term falls
outside it (the chosen result container is then too small). -/
private def place (lc : Layout) (ia ib : Nat) (ts : Array BladeTerm) (acc : Array PlanEntry) :
    Except String (Array PlanEntry) :=
  ts.foldlM (init := acc) fun acc t =>
    if lc.contains V.n t.bits then
      .ok (acc.push { ia, ib, ic := lc.rank V.n t.bits, coef := t.coef, z := t.z })
    else .error s!"{V.bladeLabel t.bits} is outside the result layout {repr lc}"

/-- The plan of a binary operation from layouts `la × lb` into `lc`: one entry
per nonzero blade-pair contribution, in operand order. This is the reference
semantics every generated or interpreted kernel implements (DESIGN §5.1). -/
def plan₂ (op : BinOp) (la lb lc : Layout) : Except String (Array PlanEntry) := do
  let bs := lb.blades V.n
  let mut acc := #[]
  for a in la.blades V.n, ia in [0:la.size V.n] do
    for b in bs, ib in [0:bs.size] do
      acc ← place V lc ia ib (← V.terms₂ op a b) acc
  return acc

/-- The plan of a unary operation from layout `la` into `lc`. -/
def plan₁ (op : UnOp) (la lc : Layout) : Except String (Array PlanEntry) := do
  let mut acc := #[]
  for a in la.blades V.n, ia in [0:la.size V.n] do
    acc ← place V lc ia 0 (← V.terms₁ op a) acc
  return acc

/-- Julia's result container for a binary operation on two `Chain`s of grades
`g`, `h` in a non-tangent space (DESIGN §4.2): `∧` gives grade `g+h`, `∨`
grade `g+h-n` (with `𝟎` below), the contractions grade `g-h` (`h-g` for `⨼`
and `<<`), `×` grade `n-g-h`, `antidot` grade `n-(h-g)`, and the geometric
products the half of parity `g+h` (`n+g+h` for `⟇`). -/
def chainResult (op : BinOp) (g h : Nat) : Layout :=
  let n := V.n
  let half := fun (k : Nat) => if k % 2 == 0 then Layout.even else .odd
  match op with
  | .wedge => .chain (g + h)
  | .vee => .chain (g + h - n)
  | .contraction | .contractionRevRight => .chain (g - h)
  | .contractionLeft | .contractionRevLeft => .chain (h - g)
  | .scalarContraction => .chain 0
  | .cross => .chain (n - (g + h))
  | .antidot => .chain (n - (h - g))
  | .mul | .reverseMul => half (g + h)
  | .veedot => half (n + g + h)

end TensorBundle

/-! ## Typed blades -/

/-- A `TensorBundle` knows its dimension (AbstractTensors `mdims`). -/
instance : AbstractTensors.HasMDims TensorBundle := ⟨TensorBundle.n⟩

/-- Julia `Submanifold{V,G,B} <: TensorTerm{V,G,Int}`: a unit blade is a
graded single-term element with `Int` scalars. -/
instance {V : TensorBundle} {G : Nat} : AbstractTensors.TensorTerm (Submanifold V G) TensorBundle V G Int
  where

namespace Submanifold

variable {V : TensorBundle} {G H : Nat}

/-- The blade with label-mode name `s` (`labels(V)`: `v12`, `∂1v2`, `v∞∅1`, …;
Julia `Λ(V).v12`) if it has grade `G`. Names that need a sign or a metric
factor (`v21`, `v11`) are not blades; use `TensorBundle.lookup` for those. -/
def ofLabel? (s : String) : Option (Submanifold V G) := (V.labelBlade? s).bind ofBits?

/-- `op a b` on typed blades (Julia's result kind). -/
@[inline] def apply₂ (op : BinOp) (a : Submanifold V G) (b : Submanifold V H) : Except String BladeResult :=
  V.apply₂ op a.bits b.bits

/-- `op b` on a typed blade. -/
@[inline] def apply₁ (op : UnOp) (b : Submanifold V G) : Except String BladeResult := V.apply₁ op b.bits

/-- Geometric product of typed blades. -/
@[inline] def mul (a : Submanifold V G) (b : Submanifold V H) : BladeResult := V.mul a.bits b.bits

/-- Exterior product: `𝟎` or `±e_{a∪b}`, of grade `G+H` (tangent spaces aside). -/
@[inline] def wedge (a : Submanifold V G) (b : Submanifold V H) : BladeResult := V.wedge a.bits b.bits

/-- Regressive product. -/
@[inline] def vee (a : Submanifold V G) (b : Submanifold V H) : BladeResult := V.vee a.bits b.bits

/-- Julia `contraction(a,b)`. -/
@[inline] def contraction (a : Submanifold V G) (b : Submanifold V H) : BladeResult :=
  V.contraction a.bits b.bits

/-- Julia `~b`. -/
@[inline] def reverse (b : Submanifold V G) : BladeResult := V.reverse b.bits

/-- Julia `⋆b`. -/
@[inline] def hodge (b : Submanifold V G) : Except String BladeResult := V.complementrighthodge b.bits

end Submanifold

end DirectSum
