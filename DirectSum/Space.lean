/-
The space layer: `Metric` and `TensorBundle` (DESIGN.md §3), ported from
DirectSum.jl `src/DirectSum.jl` and `src/generic.jl`.

A Julia space is a zero-size type `Signature{N,Options,Metrics,Vars,Diff,Name}`
(or `DiagonalForm`, or Grassmann's `MetricTensor`, or a bare `Int n`); here it is
one ordinary value, usable as a type index of the element types.

Generator (bit) layout, bit `k-1` ⇔ generator `k` (port-notes/directsum.md §3.5):

```
non-dyadic:  [∞] [∅] v₁ … v_m  ∂₁ … ∂_ν        (∞/∅ only when present)
dyadic:      v₁ … v_m  w¹ … wᵐ  ∂₁ … ∂_ν  ϵ¹ … ϵ^ν
```
-/
import DirectSum.Bits
import Leibniz.Combinatorics
import Leibniz.Generic
import Leibniz.Indices

namespace DirectSum

open Bits

/-- Metric of a tensor bundle.

* `signature neg`: Julia `Signature`; bit `k` set ⇔ `e_{k+1}² = -1`. In
  conformal spaces the `∅` slot carries a `-` bit (`S"∞∅+++"` has
  `neg = 0b00010`), exactly as Julia stores it.
* `diagonal d`: Julia `DiagonalForm`; the **primal** diagonal values of the
  non-tangent generators (a dual space negates them on read, as Julia's
  `diagonalform` does). Zeros are allowed (degenerate metrics).
* `tensor g`: Grassmann's `MetricTensor`, a symmetric Gram matrix (row-major).
* `euclid`: Julia's bare `Int n` space (Euclidean; displayed `⟨111⟩`). -/
inductive Metric where
  /-- Julia `Signature` metric bits. -/
  | signature (neg : UInt64)
  /-- Julia `DiagonalForm` values. -/
  | diagonal (d : Array Rat)
  /-- Grassmann `MetricTensor` Gram matrix. -/
  | tensor (g : Array (Array Rat))
  /-- Julia `Int n` (Euclidean, printed with `1`s). -/
  | euclid
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- A tensor bundle / vector space: Julia `TensorBundle{n,Options,Metrics,Vars,Diff,Name}`
(`DirectSum.jl src/DirectSum.jl:64`). -/
structure TensorBundle where
  /-- `mdims`: total generators, including `∞`/`∅` and all tangent slots. -/
  n : Nat
  /-- The metric (Julia `Metrics` parameter). -/
  metric : Metric
  /-- `∞` null generator present (generator 1). -/
  hasinf : Bool := false
  /-- `∅` null generator present (generator 2 if `hasinf`, else 1). -/
  hasorigin : Bool := false
  /-- `-1` dyadic `V⊕V'` (printed `*`), `+1` dual `V'` (printed `'`), `0` plain. -/
  dyadmode : Int := 0
  /-- Julia `polymode` (only affects tangent index glyphs). -/
  polymode : Bool := true
  /-- `ν`: number of tangent variables (Julia `Vars`). -/
  diffvars : Nat := 0
  /-- `μ`: Leibniz–Taylor order (Julia `Diff`). -/
  diffmode : Nat := 0
  /-- Naming scheme (1 = `v w ∂ ϵ`, 2 = `X x Y y`; Julia `Name`). -/
  name : Nat := 1
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace TensorBundle

/-! ## Constructors -/

/-- Julia `Int n` (and the handles `ℝ0 … ℝ9 = Submanifold(n)`): Euclidean,
displayed `⟨111⟩`. -/
def euclidean (n : Nat) : TensorBundle := { n, metric := .euclid }

/-- A plain `Signature` with `n` generators and negative-square mask `neg`
(Julia `Signature{n,0,neg}`); `sig n` is Julia `ℝ^n`. -/
def sig (n : Nat) (neg : UInt64 := 0) : TensorBundle :=
  { n, metric := .signature (neg &&& lowMask n) }

/-- Julia `Signature(n,d,o,s)` (`DirectSum.jl src/DirectSum.jl:141`): `d`/`o`
select `∞`/`∅` (which are among the `n` generators). -/
def ofCode (n : Nat) (inf origin : Bool) (neg : UInt64 := 0) : TensorBundle :=
  { n, metric := .signature neg, hasinf := inf, hasorigin := origin }

/-- Julia `DiagonalForm(values…)`. -/
def diag (d : Array Rat) : TensorBundle := { n := d.size, metric := .diagonal d }

/-- Grassmann `MetricTensor(g)` from a symmetric Gram matrix. -/
def metricTensor (g : Array (Array Rat)) : TensorBundle := { n := g.size, metric := .tensor g }

/-- Julia `V0 = Signature(0)`. -/
def V0 : TensorBundle := sig 0

variable (V : TensorBundle)

/-! ## Options and modes (`DirectSum.jl src/generic.jl:37-62`) -/

/-- Julia `mdims`/`rank`: total number of generators. -/
@[inline] def mdims : Nat := V.n

/-- Julia `isdual`: `dyadmode > 0`. -/
@[inline] def isdual : Bool := V.dyadmode > 0

/-- Julia `isdyadic`: `dyadmode < 0` (`V⊕V'`). -/
@[inline] def isdyadic : Bool := V.dyadmode < 0

/-- Julia `istangent`: `diffvars ≠ 0`. -/
@[inline] def istangent : Bool := V.diffvars != 0

/-- Julia `hasconformal = hasinf && hasorigin` (`Leibniz.jl src/generic.jl:53`). -/
@[inline] def hasconformal : Bool := V.hasinf && V.hasorigin

/-- Number of null generators `hasinf + hasorigin` (Julia's `P`). -/
@[inline] def nulls : Nat := (if V.hasinf then 1 else 0) + (if V.hasorigin then 1 else 0)

/-- The Julia options integer `tensorhash` (`DirectSum.jl src/DirectSum.jl:83-85`):
`1` ∞, `2` ∅, `4` dual, `8` dyadic, `16` polymode off. -/
def options : Nat :=
  (if V.hasinf then 1 else 0) + (if V.hasorigin then 2 else 0) + (if V.isdual then 4 else 0)
    + (if V.isdyadic then 8 else 0) + (if V.polymode then 0 else 16)

/-- Number of tangent slots: `ν` per side (`2ν` for dyadic spaces). -/
@[inline] def tangentSlots : Nat := (if V.isdyadic then 2 else 1) * V.diffvars

/-- Julia `grade(V) = rank - (isdyadic ? 2 : 1)·diffvars` (`Leibniz.jl src/generic.jl:12`):
the number of non-tangent generators. -/
@[inline] def grade : Nat := V.n - V.tangentSlots

/-- Julia `pseudograde(V::Manifold) = mdims - rank - k·diffvars` (negative for
tangent spaces, `Leibniz.jl src/generic.jl:11`). -/
@[inline] def pseudograde : Int := -((V.tangentSlots : Nat) : Int)

/-- Julia `diffmask(V)` as a pair `(∂ block, ϵ block)` (`Leibniz.jl src/generic.jl:70-80`);
the second component is 0 unless the space is dyadic. -/
def diffmaskPair : UInt64 × UInt64 :=
  let d := V.diffvars
  if V.isdyadic then (shl (lowMask d) (V.n - 2 * d), shl (lowMask d) (V.n - d))
  else (shl (lowMask d) (V.n - d), 0)

/-- All tangent bits (the OR of both `diffmask` blocks). -/
@[inline] def diffmask : UInt64 := V.diffmaskPair.1 ||| V.diffmaskPair.2

/-- Julia `isdiag`: `Int` and `DiagonalForm` are diagonal, a `Signature` is
unless it is conformal, a `MetricTensor` never is (`DirectSum.jl src/generic.jl:66-68`). -/
def isdiag : Bool :=
  match V.metric with
  | .euclid | .diagonal _ => true
  | .signature _ => !V.hasconformal
  | .tensor _ => false

/-- The naming scheme `(vec, cov, duo, dif)` (Julia `namelist`). -/
@[inline] def names : Leibniz.Names := Leibniz.nameScheme V.name

/-- Julia `loworder(V)`: tangent order lowered by one (floor 0). -/
def loworder : TensorBundle := { V with diffmode := V.diffmode - 1 }

/-! ## The three metric views (port-notes/grassmann-parity.md §3.3) -/

/-- The effective diagonal of a `DiagonalForm` (negated when dual, Julia
`diagonalform`). Empty for other metrics. -/
def diagValues : Array Rat :=
  match V.metric with
  | .diagonal d => if V.isdual then d.map (- ·) else d
  | _ => #[]

/-- **View B**: `V[i]` for 1-based generator `i` (Julia `getindex` on the full
`Submanifold`): `±1` for a `Signature` (conformal `∅` included, it carries a `-`
bit), the diagonal value of a `DiagonalForm`, `1` for `Int`, and the diagonal
entry of a `MetricTensor`. -/
def metricAt (i : Nat) : Rat :=
  match V.metric with
  | .euclid => 1
  | .signature s => if testBit s (i - 1) then -1 else 1
  | .diagonal d => let x := d[i - 1]?.getD 1; if V.isdual then -x else x
  | .tensor g => let x := (g[i - 1]?.bind (·[i - 1]?)).getD 1; if V.isdual then -x else x

/-- **View A**: the metric bits of Julia `Signature(V)` used by `parity`:
the signature bits, except `0` for conformal and non-diagonal spaces; for a
`DiagonalForm` the sign bits of its effective values. -/
def sigBits : UInt64 :=
  match V.metric with
  | .euclid | .tensor _ => 0
  | .signature s => if V.hasconformal then 0 else s
  | .diagonal _ =>
    V.diagValues.zipIdx.foldl (fun acc (x, i) => if x < 0 then acc ||| shl 1 i else acc) 0

/-- **View C**, mathematically correct: the Gram matrix `g(eᵢ, eⱼ)`. A conformal
null pair has `g(e∞,e∅) = -1` (`+1` in a dual space), `g(e∞,e∞) = g(e∅,e∅) = 0`,
and every other generator keeps its signature (`±1`). -/
def gram : Array (Array Rat) :=
  match V.metric with
  | .tensor g => if V.isdual then g.map (·.map (- ·)) else g
  | _ =>
    (List.range V.n).toArray.map fun i => (List.range V.n).toArray.map fun j =>
      if V.hasconformal && i < 2 && j < 2 then
        (if i == j then 0 else if V.isdual then 1 else -1)
      else if i == j then V.metricAt (i + 1) else 0

/-- **View C as Julia computes it** (`metrictensor`/`metricdyad`, Grassmann
`src/forms.jl:1582-1593`): identical to `gram` except that a conformal space
hard-codes `-1` on the null pair and `+1` on every other diagonal entry,
ignoring the signature bits. This is Julia defect C4neg; it is kept only so
the bug-compatible `paritygeometric` port can be checked against the oracle. -/
def gramJulia : Array (Array Rat) :=
  if V.hasconformal then
    (List.range V.n).toArray.map fun i => (List.range V.n).toArray.map fun j =>
      if i < 2 && j < 2 then (if i == j then 0 else -1) else if i == j then 1 else 0
  else V.gram

/-- Julia `det(V)`: `(-1)^popcount(S)` for a `Signature` (over all bits), the
product of the diagonal for a `DiagonalForm` (`DirectSum.jl src/generic.jl:87-88`). -/
def det : Rat :=
  match V.metric with
  | .euclid => 1
  | .signature s => if popcount s % 2 == 1 then -1 else 1
  | .diagonal _ => V.diagValues.foldl (· * ·) 1
  | .tensor _ => 1

/-! ## Labels -/

/-- The printing context of the full space for `Leibniz.printLabel`. -/
def labelCtx : Leibniz.LabelCtx :=
  { n := V.n, diffvars := V.diffvars, dyadmode := V.dyadmode,
    hasinf := V.hasinf, hasorigin := V.hasorigin }

/-- Display name of basis blade `b` (Julia `show` of a basis `Submanifold`),
e.g. `v₁₂`, `w¹`, `∂₁v₂`, `v∞∅₁`; `label = true` gives the ASCII label `v12`. -/
def bladeLabel (b : UInt64) (label : Bool := false) : String :=
  Leibniz.printLabel V.labelCtx b label V.names

/-- Julia `labels(V)` (`DirectSum.jl src/basis.jl:19-32`): ASCII labels in basis
order; element 1 is always the vector prefix (`v`, even for a dual space). -/
def labels : Array String :=
  (Leibniz.indexBasisAll V.n).map fun b => if b == 0 then V.names.1 else V.bladeLabel b true

/-! ## Well-formedness -/

/-- The structural invariants every constructor maintains: `n ≤ 62` (Julia's
printable index range), a diagonal of the right size, a square Gram matrix,
`dyadmode ∈ {-1,0,1}`, room for the null generators, a dyadic space splits
evenly, and conformal spaces are neither dyadic nor tangent-dyadic. -/
def valid : Bool :=
  V.n ≤ 62 && V.tangentSlots ≤ V.n && (V.dyadmode == -1 || V.dyadmode == 0 || V.dyadmode == 1)
    && V.nulls ≤ V.grade
    && (!V.isdyadic || (V.grade % 2 == 0 && V.nulls == 0))
    && (match V.metric with
        | .signature s => s &&& ~~~(lowMask V.n) == 0
        | .diagonal d => d.size == V.grade
        | .tensor g => g.size == V.n && g.all (·.size == V.n)
        | .euclid => V.dyadmode == 0 && V.nulls == 0)

end TensorBundle

end DirectSum
