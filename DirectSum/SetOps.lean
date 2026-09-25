/-
Set theory on spaces, subspaces and blades: `∪`, `∩`, `⊆`, `⊇`, Julia's space
equality, the direct sum of subspaces, the `+` alias of `⊕` and `V^i`
(DirectSum.jl `src/operations.jl:36-168`, Leibniz.jl `src/generic.jl:109-130,
192-198`).

Julia dispatches these on the type parameters of a space,
`TensorBundle{N,M,S,F,D}` (`N` generators, options `M`, metric `S`, tangent
variables `F`, order `D`); the Lean functions compare the same fields of the
space value. `Int` spaces (`ℝ3`) take part as the `Signature` of the same size.

Julia errors become `Except String`. The notations are total: `a ∪ b` and
`a ∩ b` (core `Union`/`Inter`) panic with Julia's message on an unsupported
pair, and `a ⊆ b`, `a ⊇ b` (scoped in `DirectSum`, heterogeneous: spaces,
subspaces and blades mix) are decidable propositions that are `False` on an
error.

Julia defects fixed here (documented in `docs/port-notes/directsum.md`):

* `∪`/`∩` of two `DiagonalForm`s that differ only in their tangent variables
  throw `UndefVarError: DiagnoalForm` (a typo in `operations.jl:104,131`); the
  port returns the intended `DiagonalForm`.
* `ℝ3 ⊆ ℝ4` is `false` and `ℝ3 ∪ ℝ4 = ℝ7` in Julia (`⊆(::Submanifold{V}, ::Int)`
  falls back to `Base.issubset` on two integers); the port compares `Int`
  spaces as the `Signature`s they stand for (`ℝ3 ⊆ ℝ4`, `ℝ3 ∪ ℝ4` is an error
  like `ℝ^3 ∪ ℝ^4`).
* A union of subspaces of unrelated spaces recurses through `interop` until
  Julia's stack overflows; the port reports an error.
-/
import DirectSum.SpaceOps
import DirectSum.Blade

namespace DirectSum

open Bits

namespace TensorBundle

/-! ## Embeddings of masks (`Leibniz.jl src/generic.jl:109-130`) -/

/-- Julia `mixed(V, b)` (`Leibniz.jl src/generic.jl:109-117`): the mask `b` of
`V` (or of the dual space `V'`) embedded into the dyadic space `V ⊕ V'`, whose
layout is `v₁…v_m w¹…wᵐ ∂₁…∂_ν ϵ¹…ϵ^ν`. A primal mask keeps its generators and
moves its tangent bits to the `∂` block; a dual mask moves to the `w` and `ϵ`
blocks. Julia throws a `MethodError` for a dyadic tangent `V` (quirk Q12);
here the dyadic `diffmask` is the union of both blocks, which makes the
embedding of an already dyadic mask the identity on its generators. -/
def mixed (V : TensorBundle) (b : UInt64) : UInt64 :=
  let N := V.n
  let D := V.diffvars
  if D != 0 then
    let A := b &&& lowMask (N - D)
    let B := b &&& V.diffmask
    if V.isdual then shl A (N - D) ||| shl B N else A ||| shl B (N - D)
  else if V.isdual then shl b N else b

/-- Julia `combine(v, w, a, b)` (`Leibniz.jl src/generic.jl:119-130`): the masks
`a` of `v` and `b` of `w` side by side in `v ⊕ w`. Julia throws when one space
is dual and the other is not. With tangent variables the Grassmann parts are
concatenated and the tangent bits follow at `mdims(w)` (Julia's layout). -/
def combine (v w : TensorBundle) (a b : UInt64) : Except String UInt64 :=
  if v.isdual != w.isdual then .error s!"{v} and {w} incompatible"
  else if v.istangent || w.istangent then
    let gV := v.grade
    let gW := w.grade
    let diffs := (a &&& w.diffmask) ||| (b &&& w.diffmask)
    .ok ((a &&& lowMask gV) ||| shl (b &&& lowMask gW) gV ||| shl diffs w.n)
  else .ok (a ||| shl b v.n)

-- Oracle (port-notes/leibniz.md §6): `mixed(tangent(ℝ^3), 0b1011) = 0x43`,
-- its dual gives `0x98`, `mixed((ℝ^3)', 0b101) = 0x28`, `combine(3,4,5,3) = 0x1d`.
example : (sig 3).tangent.mixed 0b1011 = 0x43 := by decide
example : (sig 3).tangent.dual.mixed 0b1011 = 0x98 := by decide
example : (sig 3).dual.mixed 0b101 = 0x28 := by decide
example : (combine (euclidean 3) (euclidean 4) 5 3).toOption = some 0x1d := by decide

/-! ## `+` and `^` -/

/-- Julia `V + W` is the direct sum `V ⊕ W` (`DirectSum.jl src/operations.jl:36`),
e.g. `V + V′ = ⟨+++---⟩*`; panics with Julia's message on an unsupported sum. -/
instance : HAdd TensorBundle TensorBundle TensorBundle := ⟨oplus!⟩

/-- Total `V^i` for notation: panics with Julia's message when `V` has options
(`S!"∞+"^2`: Julia recurses through `interop` until its stack overflows). -/
def pow! (V : TensorBundle) (i : Nat) : TensorBundle :=
  match V.pow i with
  | .ok W => W
  | .error e => panic! e

/-- Julia `V^i = V ⊕ ⋯ ⊕ V` (`DirectSum.jl src/operations.jl:75-87`):
`(ℝ^2)^2 = ⟨++++⟩`, `V^0 = V0`. The literal `ℝ^n` is separate syntax. -/
instance : HPow TensorBundle Nat TensorBundle := ⟨pow!⟩

/-! ## Space set operations (`DirectSum.jl src/operations.jl:91-168`) -/

/-- The space as Julia dispatches on it: an `Int` space counts as the
`Signature` of the same size. -/
private def asSig (V : TensorBundle) : TensorBundle :=
  match V.metric with
  | .euclid => { V with metric := .signature 0 }
  | _ => V

/-- Same `N`, options and metric (Julia `TensorBundle{N,M,S}` on both sides). -/
private def sameNMS (a b : TensorBundle) : Bool :=
  let a := asSig a
  let b := asSig b
  a.n == b.n && a.options == b.options && a.metric == b.metric

/-- Same options and metric, but different tangent parameters `(F, D)` (the
first branch of Julia's general methods). -/
private def sameMSOtherTangent (a b : TensorBundle) : Bool :=
  let a := asSig a
  let b := asSig b
  a.options == b.options && a.metric == b.metric &&
    (a.diffvars != b.diffvars || a.diffmode != b.diffmode)

/-- The space with `N`, `F`, `D` combined by `f` (Julia
`Signature{f(N1,N2),M,S,f(F1,F2),f(D1,D2)}()`, naming scheme reset). -/
private def tangentHull (f : Nat → Nat → Nat) (a b : TensorBundle) : TensorBundle :=
  { asSig a with n := f a.n b.n, diffvars := f a.diffvars b.diffvars,
                 diffmode := f a.diffmode b.diffmode, name := 1 }

/-- Julia `a ⊆ b` for spaces (`DirectSum.jl src/operations.jl:143-168`), with a
fuel bound for the one recursive case (`V ⊆ W` for a dyadic `W` compares
`V ⊕ V'` with `W` by Julia `==`).

* the same space (`N`, options, metric): `true`; the same `N` otherwise: `false`;
* two `Signature`s differing only in `N`: `N₁ ≤ N₂` (`ℝ^3 ⊆ ℝ^4`,
  `S"+-" ⊆ S"+-+"`: the metric bits are compared as integers);
* the same metric and options, different tangent parameters: both `F` and
  `D` smaller or equal (`ℝ^3 ⊆ tangent(ℝ^3)`);
* a space is never contained in a space of a different duality, and a dyadic
  space never in a non-dyadic one; a plain or dual `V` is contained in a dyadic
  `W` iff `V ⊕ V' == W` (`V' ⊕ V` for dual `V`);
* everything else is Julia's "arbitrary TensorBundle subsets" error. -/
def subsetFuel : Nat → TensorBundle → TensorBundle → Except String Bool
  | fuel, a, b =>
    if sameNMS a b then .ok true
    else if a.n == b.n then .ok false
    else
      let a' := asSig a
      let b' := asSig b
      if (match a'.metric with | .signature _ => true | _ => false) &&
          (match b'.metric with | .signature _ => true | _ => false) &&
          a'.options == b'.options && a'.metric == b'.metric &&
          a.diffvars == b.diffvars && a.diffmode == b.diffmode then
        .ok (a.n ≤ b.n)
      else if sameMSOtherTangent a b then .ok (a.diffvars ≤ b.diffvars && a.diffmode ≤ b.diffmode)
      else
        let c1 := a.dyadmode
        let c2 := b.dyadmode
        if (c1 != c2 && c1 ≥ 0 && c2 ≥ 0) || (c1 < 0 && c2 ≥ 0) then .ok false
        else if c2 < 0 && c1 ≥ 0 then
          match fuel with
          | 0 => .error "arbitrary TensorBundle subsets not yet implemented."
          | fuel + 1 => do
            let s ← if c1 > 0 then oplus a.dual a else oplus a a.dual
            let x ← subsetFuel fuel s b
            let y ← subsetFuel fuel b s
            return x && y
        else .error "arbitrary TensorBundle subsets not yet implemented."

/-- Julia `a ⊆ b` for spaces (see `subsetFuel`), or Julia's error. -/
def subset? (a b : TensorBundle) : Except String Bool := subsetFuel 2 a b

/-- Julia `a ⊇ b = b ⊆ a` (`DirectSum.jl src/operations.jl:142`). -/
def superset? (a b : TensorBundle) : Except String Bool := subset? b a

/-- Julia `a == b` on spaces, `equal(a, b) = a ⊆ b && a ⊇ b`
(`DirectSum.jl src/DirectSum.jl:366`): `ℝ3 == ℝ^3`, `ℝ^3 == S"+++"`. Short-circuits like Julia's `&&`. This is
the documented Julia equality; the derived `DecidableEq`/`==` on
`TensorBundle` is structural (it keys instances and separates `ℝ3` from
`ℝ^3`). -/
def equal? (a b : TensorBundle) : Except String Bool := do
  if (← subset? a b) then subset? b a else return false

/-- Julia `a == b` on spaces (`equal?`), `false` where Julia throws. -/
def equal (a b : TensorBundle) : Bool :=
  match equal? a b with
  | .ok r => r
  | .error _ => false

/-- Julia `a ∪ b` for spaces (`DirectSum.jl src/operations.jl:91,100-116`).

* the same space: `a`;
* the same metric and options, different tangent parameters: the space with
  the larger `N`, `F`, `D` (`ℝ^3 ∪ tangent(ℝ^3) = T¹⟨+++₁⟩`);
* a space and its dual: the dyadic `V ⊕ V'` (`ℝ ∪ ℝ' = ⟨+-⟩*`, primal half
  first whatever the order);
* a dyadic space and a space it contains: the dyadic space, or Julia's
  "incompatible" error;
* everything else is one of Julia's errors. -/
def union (a b : TensorBundle) : Except String TensorBundle := do
  if sameNMS a b then return a
  if sameMSOtherTangent a b then return tangentHull max a b
  let c1 := a.dyadmode
  let c2 := b.dyadmode
  if c1 != c2 && c1 ≥ 0 && c2 ≥ 0 && (← equal? a b.dual) then
    return ← (if c1 > 0 then oplus b a else oplus a b)
  if min c1 c2 < 0 && max c1 c2 ≥ 0 then
    let y ← if c1 < 0 then subset? b a else subset? a b
    if !y then throw s!"TensorBundle union {a}∪{b} incompatible!"
    return if c1 < 0 then a else b
  if a.n == b.n then throw s!"TensorBundle intersection {a}∩{b} incompatible!"
  throw "arbitrary TensorBundle union not yet implemented."

/-- Julia `a ∩ b` for spaces (`DirectSum.jl src/operations.jl:118-140`).

* the same space: `a`; the same `N` otherwise: `V0` (`ℝ ∩ ℝ' = ⟨⟩`);
* the same metric and options, different tangent parameters: the space with
  the smaller `N`, `F`, `D`;
* spaces of different dualities (neither dyadic): `V0`;
* a dyadic `W` and `V`: `V` when `V ⊕ V' == W`, else `V0`;
* everything else is Julia's "arbitrary TensorBundle intersection" error. -/
def inter (a b : TensorBundle) : Except String TensorBundle := do
  if sameNMS a b then return a
  if a.n == b.n then return V0
  if sameMSOtherTangent a b then return tangentHull min a b
  let c1 := a.dyadmode
  let c2 := b.dyadmode
  if c1 != c2 && c1 ≥ 0 && c2 ≥ 0 then return V0
  if min c1 c2 < 0 && max c1 c2 ≥ 0 then
    let y := c1 < 0
    let (x, d) := if y then (b, a) else (a, b)
    return if (← equal? (← oplus x x.dual) d) then x else V0
  throw "arbitrary TensorBundle intersection not yet implemented."

/-- Total `∪` for notation: panics with Julia's message. -/
def union! (a b : TensorBundle) : TensorBundle :=
  match union a b with
  | .ok v => v
  | .error e => panic! e

/-- Total `∩` for notation: panics with Julia's message. -/
def inter! (a b : TensorBundle) : TensorBundle :=
  match inter a b with
  | .ok v => v
  | .error e => panic! e

/-- `a ∪ b` on spaces (Julia `∪`). -/
instance : Union TensorBundle := ⟨union!⟩

/-- `a ∩ b` on spaces (Julia `∩`). -/
instance : Inter TensorBundle := ⟨inter!⟩

/-- Julia's variadic `∪(a, b, c…) = ∪(a ∪ b, c…)` (`Leibniz.jl src/generic.jl:194-195`). -/
def unionAll (a : TensorBundle) (bs : List TensorBundle) : Except String TensorBundle :=
  bs.foldlM union a

/-- Julia's variadic `∩(a, b, c…) = ∩(a ∩ b, c…)` (`Leibniz.jl src/generic.jl:197-198`). -/
def interAll (a : TensorBundle) (bs : List TensorBundle) : Except String TensorBundle :=
  bs.foldlM inter a

/-! ## Metric kinds (`DirectSum.jl src/DirectSum.jl:380-390`) -/

/-- Julia `Signature(V::DiagonalForm) = Signature{N,M}(signbit.(V[:]))`: the signs of the
(dual-negated) diagonal, options kept (`Signature(D"1,-2,3") = ⟨+-+⟩`, `Signature(D"0,1,1")
= ⟨+++⟩`); an `Int` space becomes `Signature(n)`, a `Signature` is unchanged. Julia throws for
tangent spaces (it reads `N` signs from the `grade(V)` values); the port signs the Grassmann
generators and leaves the tangent slots positive. `MetricTensor` spaces have no signature. -/
def toSignature (V : TensorBundle) : Except String TensorBundle :=
  match V.metric with
  | .signature _ => .ok V
  | .euclid => .ok { V with metric := .signature 0 }
  | .diagonal _ =>
    let bits := V.diagValues.zipIdx.foldl (fun acc (x, i) => if x < 0 then acc ||| shl 1 i else acc) 0
    .ok { V with metric := .signature bits }
  | .tensor _ => .error s!"no Signature of the MetricTensor space {V}"

/-- Julia `DiagonalForm(V::Signature) = DiagonalForm{N,M}([t ? -1 : 1 for t ∈ V[:]])`
(`DiagonalForm(S"-+-") = ⟨-1,1,-1⟩`), options kept. For a dual space Julia's `V[:]` are the
signs of the primal space, which the dual form then negates on read:
`DiagonalForm(S"-+-"') = ⟨-1,1,-1⟩'`. An `Int` space gives all ones, a
`DiagonalForm` is unchanged. Spaces with null generators or a `MetricTensor` have no diagonal
form (Julia prints a malformed `⟨∞∅1⟩` for `S"∞∅+"`). -/
def toDiagonal (V : TensorBundle) : Except String TensorBundle :=
  if V.nulls != 0 then .error s!"no DiagonalForm of the conformal space {V}" else
  match V.metric with
  | .diagonal _ => .ok V
  | .euclid => .ok { V with metric := .diagonal ((List.range V.grade).toArray.map fun _ => 1) }
  | .signature s =>
    let read := (List.range V.grade).toArray.map fun k => if testBit s k then (-1 : Rat) else 1
    .ok { V with metric := .diagonal read }
  | .tensor _ => .error s!"no DiagonalForm of the MetricTensor space {V}"

/-- Julia `subtangent(V) = V(grade(V)+1:mdims(V)…)` (`DirectSum.jl src/generic.jl`):
the subspace of the tangent generators, `subtangent(tangent(ℝ^3)) = T¹⟨___₁⟩`. -/
def subtangent (V : TensorBundle) : SubSpace V := ⟨V.diffmask⟩

end TensorBundle

/-! ## Heterogeneous `⊆` -/

/-- Julia `a ⊆ b` between spaces (`TensorBundle`), subspaces (`SubSpace V`) and
basis blades (`Submanifold V G`), whose types may differ (`v₁ ⊆ v₁₂`,
`v₁₂ ⊆ V`, `(ℝ^3)(1,2) ⊆ ℝ^3`). -/
class SubsetOf (α : Type) (β : Type) where
  /-- Julia `a ⊆ b`, or Julia's error. -/
  subset? : α → β → Except String Bool

/-- Julia `a ⊆ b` as a Boolean (`false` where Julia throws). -/
@[inline] def subsetB {α β : Type} [SubsetOf α β] (a : α) (b : β) : Bool :=
  match SubsetOf.subset? a b with
  | .ok r => r
  | .error _ => false

/-- The proposition behind the scoped `a ⊆ b`; decidable. -/
abbrev IsSubset {α β : Type} [SubsetOf α β] (a : α) (b : β) : Prop := subsetB a b = true

/-- `a ⊆ b` (Julia `⊆`, heterogeneous); overloads core's `⊆`. -/
scoped infix:50 " ⊆ " => IsSubset
/-- `a ⊇ b = b ⊆ a` (Julia `⊇`); overloads core's `⊇`. -/
scoped notation:50 a:51 " ⊇ " b:51 => IsSubset b a

instance : SubsetOf TensorBundle TensorBundle := ⟨TensorBundle.subset?⟩

namespace SubSpace

variable {V W : TensorBundle}

/-- Julia `∪` of two subspaces of the same space: the union of the masks
(`DirectSum.jl src/operations.jl:94`), `(ℝ^3)(1,2) ∪ (ℝ^3)(2,3) = ⟨+++⟩`. -/
instance : Union (SubSpace V) := ⟨fun a b => ⟨a.mask ||| b.mask⟩⟩

/-- Julia `∩` of two subspaces of the same space: the intersection of the masks
(`operations.jl:126`), `(ℝ^3)(1,2) ∩ (ℝ^3)(2,3) = ⟨_+_⟩`. -/
instance : Inter (SubSpace V) := ⟨fun a b => ⟨a.mask &&& b.mask⟩⟩

/-- Julia `⊆` of two subspaces of the same space: `count_ones(A & B) == rank(A)`
(`operations.jl:152`). -/
instance : SubsetOf (SubSpace V) (SubSpace V) := ⟨fun a b => .ok (a.mask &&& b.mask == a.mask)⟩

/-- Julia `a ⊆ B` for a subspace and a space: the parent space `V ⊆ B`
(`operations.jl:149`). -/
instance : SubsetOf (SubSpace V) TensorBundle := ⟨fun _ B => V.subset? B⟩

/-- Julia `A ⊆ b` for a space and a subspace: `A ⊆ V` when `b` is all of `V`,
else Julia's "not computable" error (`operations.jl:148`). -/
instance : SubsetOf TensorBundle (SubSpace V) :=
  ⟨fun A b => if b.rank == V.n then A.subset? V else .error s!"{A} ⊆ {b} not computable"⟩

/-- Julia `b ∪ B` for a subspace `b` of `V` and a space `B`: `V ∪ B`
(`operations.jl:93`). -/
def unionBundle (_ : SubSpace V) (B : TensorBundle) : Except String TensorBundle := V.union B

/-- Julia `B ∪ b` for a space `B` and a subspace `b` of `V`: `B ∪ V`
(`operations.jl:92`). -/
def bundleUnion (B : TensorBundle) (_ : SubSpace V) : Except String TensorBundle := B.union V

/-- Julia `A ∩ b` for a space `A` and a subspace `b`: `b` when `b ⊆ A`, else
`V0` (`none`) (`operations.jl:122-123`). -/
def interBundle (s : SubSpace V) (B : TensorBundle) : Except String (Option (SubSpace V)) := do
  return if (← V.subset? B) then some s else none

/-- Julia `mdims(::Submanifold)`: the number of included generators. -/
@[inline] def mdims (s : SubSpace V) : Nat := s.rank

/-- Julia `diffvars(::Submanifold)` (`DirectSum.jl src/DirectSum.jl`): the number
of tangent generators among the last `F` positions of the mask. -/
def diffvars (s : SubSpace V) : Nat :=
  (indicesList s.mask).countP fun i => i + V.diffvars ≥ V.n + 1

/-- Julia `M[i]` for a subspace (`DirectSum.jl src/DirectSum.jl`): the metric of
its `i`-th included generator (1-based), `0` out of range. -/
def metricAt (s : SubSpace V) (i : Nat) : Rat :=
  match (indicesList s.mask)[i - 1]? with
  | some k => V.metricAt k
  | none => 0

/-- Julia `M[:]`: the metrics of the included generators. -/
def metricList (s : SubSpace V) : List Rat := (indicesList s.mask).map V.metricAt

/-- Julia `Signature(V::Submanifold)` of a subspace of a diagonal space: the signs of the
included generators (`Signature((ℝ^3)(1,3)) = ⟨++⟩`, `Signature(D"1,-2,3"(2,3)) = ⟨-+⟩`), with
the parent's options (not its tangent variables: tangent subspaces are not ported). -/
def toSignature (s : SubSpace V) : TensorBundle :=
  let bits := s.metricList.zipIdx.foldl (fun acc (x, i) => if x < 0 then acc ||| shl 1 i else acc) 0
  { n := s.rank, metric := .signature bits, hasinf := V.hasinf && testBit s.mask 0,
    dyadmode := V.dyadmode, polymode := V.polymode }

/-- Julia `collect(M)` / `show(Λ(M))` for a subspace (`DirectSum.jl src/basis.jl`):
`DirectSum.Basis{⟨+__+⟩,4}(v, v₁, v₄, v₁₄)`, the blades of the included
generators in the parent's names. -/
def showBasis (s : SubSpace V) : String :=
  let r := s.rank
  let blades := (Leibniz.indexBasisAll r).map fun b => pdep b s.mask
  "DirectSum.Basis{" ++ toString s ++ "," ++ toString (2 ^ r) ++ "}("
    ++ ", ".intercalate (blades.map (V.bladeLabel ·)).toList ++ ")"

/-- Julia `a ⊕ b` for subspaces (`DirectSum.jl src/operations.jl:69-74`): the
subspace of `V ⊕ W` spanned by both masks, side by side (`combine`), or, for a
space and its dual, embedded by `mixed`: `(ℝ^3)(2,3) ⊕ (ℝ^3)(1) = ⟨_+++__⟩`. -/
def oplus (a : SubSpace V) (b : SubSpace W) : Except String ((U : TensorBundle) × SubSpace U) := do
  let mask ← if V.isdual == W.isdual || V != W.dual then TensorBundle.combine V W a.mask b.mask
    else .ok (V.mixed a.mask ||| W.mixed b.mask)
  let U ← match V.metric, W.metric with
    | .euclid, .euclid => V.oplus W
    | .euclid, _ => TensorBundle.oplus (asSig' V) W
    | _, .euclid => TensorBundle.oplus V (asSig' W)
    | _, _ => V.oplus W
  return ⟨U, ⟨mask⟩⟩
where
  /-- Julia `Signature(V)` of an `Int` space. -/
  asSig' (X : TensorBundle) : TensorBundle := { X with metric := .signature 0 }

/-- Julia `a ⊆ b` for subspaces of possibly different spaces
(`operations.jl:152-153`): the mask test for the same space; for different
spaces `V ⊆ W` when `b` is all of `W`, and otherwise Julia's `interop`, which
recurses until the stack overflows (an error here). -/
def subsetAny (a : SubSpace V) (b : SubSpace W) : Except String Bool :=
  if V == W then .ok (a.mask &&& b.mask == a.mask)
  else if b.rank == W.n then V.subset? W
  else .error "interop(⊆): subspaces of different spaces (Julia overflows its stack)"

/-- Julia `a ∪ b` for subspaces of possibly different spaces (`operations.jl:94-99`):
the union of the masks for the same space; otherwise `b` if `a ⊆ b`, `a` if
`b ⊆ a`, else the direct sum `a ⊕ b` (`b ⊕ a` when both are dual). Julia's
embedding branch for a dyadic and a non-dyadic space (`b(a) ⊆ b`) is not
ported and reports an error. -/
def unionAny (a : SubSpace V) (b : SubSpace W) : Except String ((U : TensorBundle) × SubSpace U) := do
  if V == W then return ⟨V, ⟨a.mask ||| b.mask⟩⟩
  let ma := V.dyadmode
  let mb := W.dyadmode
  if ma != mb then throw "union of subspaces of a dyadic and a non-dyadic space is not ported"
  if (← subsetAny a b) then return ⟨W, b⟩
  if (← subsetAny b a) then return ⟨V, a⟩
  if ma > 0 then b.oplus a else a.oplus b

end SubSpace

/-- Display of a subspace of any space. -/
instance : ToString ((U : TensorBundle) × SubSpace U) := ⟨fun ⟨_, s⟩ => toString s⟩

namespace Submanifold

variable {V : TensorBundle} {G H : Nat}

/-- Julia `a ∪ b` of two blades of the same space: the blade of the union of
the masks (`DirectSum.jl src/operations.jl:94`), `v₁ ∪ v₂ = v₁₂`. -/
def union (a : Submanifold V G) (b : Submanifold V H) : Submanifold V (popcount (a.bits ||| b.bits)) :=
  ⟨a.bits ||| b.bits⟩

/-- Julia `a ∩ b` of two blades of the same space (`operations.jl:126`),
`v₁₂ ∩ v₂₃ = v₂`. -/
def inter (a : Submanifold V G) (b : Submanifold V H) : Submanifold V (popcount (a.bits &&& b.bits)) :=
  ⟨a.bits &&& b.bits⟩

/-- Julia `a ⊆ b` for blades of the same space: `a`'s generators are among
`b`'s (`operations.jl:152`), `v₁ ⊆ v₁₂`. -/
instance : SubsetOf (Submanifold V G) (Submanifold V H) := ⟨fun a b => .ok (a.bits &&& b.bits == a.bits)⟩

/-- Julia `a ⊆ B` for a blade and a space: its space `V ⊆ B` (`operations.jl:149`),
`v₁₂ ⊆ V`. -/
instance : SubsetOf (Submanifold V G) TensorBundle := ⟨fun _ B => V.subset? B⟩

/-- Julia `A ⊆ b` for a space and a blade: `A ⊆ V` when `b` is the
pseudoscalar, else Julia's "not computable" error (`operations.jl:148`). -/
instance : SubsetOf TensorBundle (Submanifold V G) :=
  ⟨fun A b => if G == V.n then A.subset? V else .error s!"{A} ⊆ {b} not computable"⟩

/-- Julia `A ∩ b` for a space and a blade: `b` when `b ⊆ A`, else `V0`
(`none`) (`operations.jl:122-123`), `V ∩ v₁ = v₁`. -/
def interBundle (b : Submanifold V G) (B : TensorBundle) : Except String (Option (Submanifold V G)) := do
  return if (← V.subset? B) then some b else none

end Submanifold

end DirectSum
