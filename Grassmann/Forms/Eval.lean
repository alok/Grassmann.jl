/-
Function-call ("form") semantics of algebra elements and conversions between a
space and its subspaces (Grassmann.jl `src/forms.jl:22-142, 293-294, 836-881`,
`src/multivectors.jl:96-179, 300-329`; port-notes/grassmann-forms.md §2.2, §4.1-4.2).

* `t(y₁, …, y_k) = t ⋅ (y₁ ∧ … ∧ y_k)` (`forms.jl:293-294`): an element evaluated on
  vectors, a multilinear form (`Chain.eval`, `Multivector.eval`).
* `W(x)` for a subspace `W ⊆ V` (`forms.jl:23-142`): the projection onto the
  blades inside `W` (a blade survives when all its generators are in `W`, and is
  renumbered by the parallel bit extract `pext`); for `V ⊆ W` the embedding
  (renumbered by `pdep`). The subspace is its own `TensorBundle` (`restrict`, Julia
  `TensorBundle(b::Submanifold)`, `forms.jl:1674-1688`). Julia's projection of
  grade ≥ 2 and multivector elements uses the defective `lowerbits` (wrong, cache
  order dependent: port-notes §3.1, §8.4 item 13); this is the correct `pext`.
  Julia prints the elements of a subspace with the parent's generator indices
  (`V(2,3)(x) = 2v₂ + 3v₃`); the restricted bundle here numbers them from 1.
* `vecdot(x, y)` (`forms.jl:838-881`): the metric-free coefficient dot on the
  common grades (zero across different grades or parities; Julia's
  `vecdot(::CoSpinor, ::Multivector)` uses the even part and is always zero:
  here the odd part).
-/
import Grassmann.Forms.Show

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors Grassmann.Forms

namespace Forms

/-- The subspace bundle of the generators in `mask` (Julia `TensorBundle(b::Submanifold)`,
`forms.jl:1674-1688`): Euclidean, the extracted signature bits, the selected
diagonal values or the restricted Gram matrix. -/
def restrict (V : TensorBundle) (mask : UInt64) : TensorBundle :=
  let S := mask &&& lowMask V.n
  let idx := (List.range V.n).filter fun i => testBit S i
  let M := idx.length
  match V.metric with
  | .euclid => TensorBundle.euclidean M
  | .signature neg =>
    { V with n := M, metric := .signature (pext neg S),
             hasinf := V.hasinf && testBit S 0,
             hasorigin := V.hasorigin && testBit S (if V.hasinf then 1 else 0) }
  | .diagonal d => { V with n := M, metric := .diagonal (idx.toArray.map fun i => d[i]?.getD 1) }
  | .tensor g =>
    { V with n := M, metric := .tensor (idx.toArray.map fun i => idx.toArray.map fun j =>
        (g[i]?.bind (·[j]?)).getD 0) }

/-- Julia `↓(V)`: the space without its first (homogeneous) generator. -/
@[inline] def drop1 (V : TensorBundle) : TensorBundle := restrict V (lowMask V.n &&& ~~~1)

end Forms

variable {V W : TensorBundle} {G : Nat} {α : Type} [Coeff α]

/-! ## Subspace projection and embedding -/

namespace Chain

/-- Julia `W(x)` for a subspace `W ⊆ V` given by a mask (`forms.jl:48-66`): the
blades of `x` inside `W`, renumbered by `pext`. -/
def project (x : Chain V G α) (S : SubSpace V) : Chain (Forms.restrict V S.mask) G α :=
  let S' := S.mask &&& lowMask V.n
  let bsW := Leibniz.indexBasis (Forms.restrict V S.mask).n G
  Chain.ofFn fun i =>
    let b := pdep bsW[i.1]! S'
    x.coeff b

/-- Julia `W(x)` for `V ⊆ W` (`forms.jl:67-85`): the embedding of an element of a
subspace, its blades renumbered by `pdep` into the mask `S` of `W`. -/
def embedSub (S : SubSpace W) (x : Chain (Forms.restrict W S.mask) G α) : Chain W G α :=
  let S' := S.mask &&& lowMask W.n
  Chain.ofFn fun i =>
    let b := (Leibniz.indexBasis W.n G)[i.1]!
    if popcount (b &&& S') == G then x.coeff (pext b S') else Coeff.zero

/-- Julia `W(x)` for a space `V` whose generators are the first ones of `W`
(`ℝ^4(x)`, `(V ⊕ V')(x)`; `forms.jl:67-85` with `mixed(V, B) = B`): the same blades,
zero on the new generators. A dual `V` inside a dyadic `W` shifts by `V.n`. -/
def embed (x : Chain V G α) (W : TensorBundle) : Chain W G α :=
  let shift := if V.isdual && W.isdyadic then V.n else 0
  Chain.ofFn fun i =>
    let b := (Leibniz.indexBasis W.n G)[i.1]!
    let b' := b >>> shift.toUInt64
    if b' <<< shift.toUInt64 == b && b' &&& ~~~(lowMask V.n) == 0 then x.coeff b' else Coeff.zero

end Chain

namespace Multivector

/-- Julia `W(m)` for a subspace `W ⊆ V` (`forms.jl:98-111`), with `pext`. -/
def project (m : Multivector V α) (S : SubSpace V) : Multivector (Forms.restrict V S.mask) α :=
  let S' := S.mask &&& lowMask V.n
  let bsW := Leibniz.indexBasisAll (Forms.restrict V S.mask).n
  Multivector.ofFn fun i => m.coeff (pdep bsW[i.1]! S')

/-- Julia `W(m)` for `V` the first generators of `W` (`forms.jl:112-134`). -/
def embed (m : Multivector V α) (W : TensorBundle) : Multivector W α :=
  Multivector.ofFn fun i =>
    let b := (Leibniz.indexBasisAll W.n)[i.1]!
    if b &&& ~~~(lowMask V.n) == 0 then m.coeff b else Coeff.zero

/-- Julia `m(g, i)` (`multivectors.jl:326-329`): the `i`-th grade-`g` term as a `Single`. -/
def term (m : Multivector V α) (g i : Nat) : Single V g α :=
  let b := Leibniz.unrank V.n g i
  ⟨b, m.coeff b⟩

end Multivector

/-! ## Multilinear forms -/

/-- `y₁ ∧ … ∧ y_k` of vectors of `V` (Julia `∧(y...)`), grade `k`. -/
def wedgeVectors [Kernels V] (ys : List (Chain V 1 α)) : Chain V ys.length α :=
  let rec go : (g : Nat) → Chain V g α → (cs : List (Chain V 1 α)) → Chain V (g + cs.length) α
    | _, acc, [] => acc
    | g, acc, c :: cs => (go (g + 1) (acc ∧ c) cs).cast (by rw [List.length_cons]; omega)
  (go 0 Chain.one ys).cast (by simp)

namespace Chain

/-- Julia `t(y₁, …, y_k) = t ⋅ (y₁ ∧ … ∧ y_k)` (`forms.jl:293`): a grade-`G` element
evaluated on `k` vectors (`B(x, y) = -24v`, `v₁₂(v₁, v₂) = v`). -/
def eval [Kernels V] (t : Chain V G α) (ys : List (Chain V 1 α)) : Chain V (G - ys.length) α :=
  contraction t (wedgeVectors ys)

end Chain

namespace Multivector

/-- Julia `m(y₁, …, y_k) = m ⋅ (y₁ ∧ … ∧ y_k)` (`forms.jl:294`). -/
def eval [Kernels V] (m : Multivector V α) (ys : List (Chain V 1 α)) : Multivector V α :=
  contraction m (wedgeVectors ys)

end Multivector

/-! ## `vecdot` -/

/-- Julia `vecdot(x, y)` (`forms.jl:838-881`): the coefficient dot
`Σ conj(xᵦ) yᵦ` over the blades of the smaller of the two layouts (the other
element restricted to it), a left fold. -/
def vecdot {X Y : Type} {lx ly : Layout} [Conj α] [InLayout X V lx α] [InLayout Y V ly α] (x : X) (y : Y) : α :=
  let xv := InLayout.vals x
  let yv := InLayout.vals y
  if lx.size V.n ≤ ly.size V.n then
    Forms.vdot xv (convertLayout V.n ly lx yv)
  else
    Forms.vdot (convertLayout V.n lx ly xv) yv

end Grassmann
