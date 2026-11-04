import Grassmann.Algebra.Norms
import Std.Data.HashMap

/-!
# Products with a runtime metric (Julia's `f(t, g)` family)

Grassmann.jl generates a second copy of every metric-dependent operation that takes the
metric as a runtime argument `g` instead of from the space type:

* `wedgedot_metric(a, b, g)` and `contraction_metric(a, b, g)` (`src/algebra.jl:39,64-91,
  225-277`; port-notes/grassmann-parity.md §4.5.4);
* the operations built on them: `abs2(t, g)`, `inv(t, g)`, `^(t, n, g)` and `/(a, b, g)`
  (`src/algebra.jl:322-379,421-551`).

When `g` is the space's own metric (`isinduced(g)`), Julia delegates to the plain
operation. In this file the metric is a **Gram matrix** `gᵢⱼ = g(eᵢ, eⱼ)` of the
generators. It may be non-diagonal, null or degenerate. The products are defined by
Chevalley's construction of the Clifford algebra of `g`:

  `eᵢ M = eᵢ ⌋ M + eᵢ ∧ M`, with `eᵢ ⌋ e_B = Σₖ (−1)ᵏ g(eᵢ, e_{bₖ}) e_{B∖bₖ}`,

where `bₖ` is the `k`-th generator of `B` in ascending order. The basis blades are outer
products `e_A = e_{a₁} ∧ … ∧ e_{aₖ}`. Since `a₁` is the lowest generator of `A`, the
identity `e_A = e_{a₁} e_{A'} − e_{a₁} ⌋ e_{A'}` (`A' = A ∖ a₁`) gives the
product of two blades recursively. With a diagonal `g` this is the space's own geometric
product. `Tests.Grassmann.Metric` checks this against the plan kernels in every
diagonal test space. With a non-diagonal `g = Pᵀ D P`, the outermorphism of `P` is
an algebra isomorphism onto the diagonal algebra of `D`, and the tests check that too.
For this reason the port does not copy Julia's sign skeleton, which replays the static
metric's signs with runtime magnitudes. That skeleton skips the entries that are
structurally zero in the static metric, so it cannot express a `g` that is fuller than
the space's own metric.

The contraction is Julia's right contraction `a ⋅ b`, extended bilinearly from blades:
`e_A ⋅ e_B = ⟨~e_B e_A⟩_{|A|−|B|}` when `|B| ≤ |A|` (`v₁₂ ⋅ v₂ = −v₁`), and `0` otherwise. The left
contraction is `a ⨼ b = b ⋅ a`, as in Julia. The outer and regressive products do not
depend on the metric, so this file has no `_metric` variants of them.

Scope: blades of up to 64 generators. Tangent (`∂`) and dyadic generators are treated
as ordinary generators of the Gram matrix. The recursion costs `O(2^{|A|})` per blade
pair, so this is a reference path for small spaces and non-induced metrics, not a kernel.
-/

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

/-- A runtime metric: the Gram matrix `g(eᵢ, eⱼ)` of the generators (0-based; entries
outside the stored rows read as `0`). It should be symmetric; only `g(eᵢ, eⱼ)` with `i`
the vector being contracted is read. -/
structure Gram (α : Type) where
  /-- The rows `g(eᵢ, ·)`. -/
  rows : Array (Array α)

namespace Gram

variable {α : Type} [Coeff α]

/-- The entry `g(eᵢ, eⱼ)`. -/
@[inline] def get (g : Gram α) (i j : Nat) : α := ((g.rows[i]?).bind (·[j]?)).getD Coeff.zero

/-- A diagonal metric `g(eᵢ, eᵢ) = dᵢ` (Julia's `DiagonalOperator` metric). -/
def diag (d : Array α) : Gram α :=
  ⟨(Array.range d.size).map fun i => (Array.range d.size).map fun j => if i == j then d[i]! else Coeff.zero⟩

/-- A metric from its entries `f i j` on `n` generators. -/
def ofFn (n : Nat) (f : Nat → Nat → α) : Gram α := ⟨(Array.range n).map fun i => (Array.range n).map (f i)⟩

/-- The space's own metric on its generators: `g(eᵢ, eⱼ)` is the scalar part of
`eᵢ eⱼ + eⱼ eᵢ` over two, read from DirectSum's blade rule (the induced metric, including
the null pair `g(∞, ∅) = −1` of a conformal space). -/
def ofSpace (V : TensorBundle) : Gram α :=
  let sc := fun (a b : UInt64) => match V.terms₂ .mul a b with
    | .ok ts => ts.foldl (fun s t => if t.bits == 0 && t.z == 0 then s + t.coef else s) 0
    | .error _ => 0
  ofFn V.n fun i j =>
    let a : UInt64 := 1 <<< i.toUInt64
    let b : UInt64 := 1 <<< j.toUInt64
    Coeff.ofRat ((sc a b + sc b a) / 2)

end Gram

namespace Metric

variable {α : Type} [Coeff α]

/-- Sparse terms `blade ↦ coefficient`. -/
abbrev Terms (α : Type) := Std.HashMap UInt64 α

/-- Add `x e_B` to a term map. -/
@[inline] def addTerm (acc : Terms α) (B : UInt64) (x : α) : Terms α :=
  acc.insert B (acc.getD B Coeff.zero + x)

/-- The generators of a blade, ascending (0-based). -/
def gens (B : UInt64) : List Nat := (List.range 64).filter fun i => (B >>> i.toUInt64) &&& 1 == 1

/-- `eᵢ ⌋ (x e_B) = x Σₖ (−1)ᵏ g(eᵢ, e_{bₖ}) e_{B∖bₖ}`, added to `acc`. -/
def vecLeftInto (g : Gram α) (i : Nat) (B : UInt64) (x : α) (acc : Terms α) : Terms α := Id.run do
  let mut acc := acc
  let mut k := 0
  for b in gens B do
    let gb := g.get i b
    if !Coeff.isZero gb then
      let c := gb * x
      acc := addTerm acc (B ^^^ (1 <<< b.toUInt64)) (if k % 2 == 0 then c else -c)
    k := k + 1
  return acc

/-- `eᵢ ∧ (x e_B)`, added to `acc` (metric-free). -/
def vecWedgeInto (i : Nat) (B : UInt64) (x : α) (acc : Terms α) : Terms α :=
  let m : UInt64 := 1 <<< i.toUInt64
  if B &&& m != 0 then acc
  else
    let below := DirectSum.Bits.popcount (B &&& (m - 1))
    addTerm acc (B ||| m) (if below % 2 == 0 then x else -x)

/-- `eᵢ M` for a term map `M`. -/
def vecMul (g : Gram α) (i : Nat) (m : Terms α) : Terms α :=
  m.fold (fun acc B x => vecWedgeInto i B x (vecLeftInto g i B x acc)) {}

/-- `e_A M` for a term map `M`: `e_A = e_{a₁} e_{A'} − e_{a₁} ⌋ e_{A'}` with `a₁` the
lowest generator of `A`. -/
partial def bladeMul (g : Gram α) (A : UInt64) (m : Terms α) : Terms α :=
  if A == 0 then m
  else
    let a := (gens A).head!
    let A' := A ^^^ (1 <<< a.toUInt64)
    let first := vecMul g a (bladeMul g A' m)
    let contr : Terms α := vecLeftInto g a A' Coeff.one {}
    contr.fold (fun acc C c =>
      (bladeMul g C m).fold (fun acc D y => addTerm acc D (-(c * y))) acc) first

/-- The geometric product of two term maps. -/
def mulTerms (g : Gram α) (a b : Terms α) : Terms α :=
  a.fold (fun acc A x =>
    if Coeff.isZero x then acc
    else (bladeMul g A b).fold (fun acc C y => addTerm acc C (x * y)) acc) {}

/-- The nonzero terms of a multivector. -/
def termsOf {V : TensorBundle} (m : Multivector V α) : Terms α :=
  m.terms.foldl (fun acc (B, x) => if Coeff.isZero x then acc else addTerm acc B x) {}

/-- A multivector from a term map (blades outside the space are dropped). -/
def ofTerms {V : TensorBundle} (t : Terms α) : Multivector V α :=
  let bs := Leibniz.indexBasisAll V.n
  Multivector.ofFn fun i => t.getD bs[i.1]! Coeff.zero

/-- The reversion sign of grade `k`. -/
@[inline] def revSign (k : Nat) : Bool := (k * (k - 1) / 2) % 2 == 0

end Metric

open Metric

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `wedgedot_metric(a, b, g)`: the geometric product of the Clifford algebra of the
runtime metric `g`. -/
def wedgedotMetric (g : Gram α) (a b : Multivector V α) : Multivector V α :=
  ofTerms (mulTerms g (termsOf a) (termsOf b))

/-- Julia `contraction_metric(a, b, g)`: the right contraction `a ⋅ b`,
`e_A ⋅ e_B = ⟨~e_B e_A⟩_{|A|−|B|}` (`0` when `|B| > |A|`). -/
def contractionMetric (g : Gram α) (a b : Multivector V α) : Multivector V α := Id.run do
  let ta := termsOf a
  let tb := termsOf b
  let mut acc : Terms α := {}
  for (A, x) in ta.toList do
    for (B, y) in tb.toList do
      let ga := DirectSum.Bits.popcount A
      let gb := DirectSum.Bits.popcount B
      if gb ≤ ga then
        let rb : α := if revSign gb then y else -y
        let p := mulTerms g ((({} : Terms α)).insert B rb) ((({} : Terms α)).insert A x)
        for (C, z) in p.toList do
          if DirectSum.Bits.popcount C == ga - gb then acc := addTerm acc C z
  return ofTerms acc

/-- The left contraction with a runtime metric, `a ⨼ b = contraction_metric(b, a, g)`. -/
@[inline] def contractionLeftMetric (g : Gram α) (a b : Multivector V α) : Multivector V α :=
  contractionMetric g b a

/-- The reverse `~a` of a multivector (metric-free). -/
def reverseTerms (a : Multivector V α) : Multivector V α :=
  ofTerms ((termsOf a).fold (fun acc B x =>
    addTerm acc B (if revSign (DirectSum.Bits.popcount B) then x else -x)) {})

/-- Julia `abs2(t, g)` for a multivector: `(~t) ⟑ t` with the runtime metric. -/
def abs2Metric (g : Gram α) (a : Multivector V α) : Multivector V α :=
  wedgedotMetric g (reverseTerms a) a

/-- Julia `^(t, n, g)`: repeated runtime-metric products (`t⁰ = 1`). -/
def powMetric (g : Gram α) (a : Multivector V α) : Nat → Multivector V α
  | 0 => Multivector.one
  | n + 1 => wedgedotMetric g (powMetric g a n) a

/-- Julia `inv(t, g)` for a versor: `~t / ⟨~t t⟩₀` when `(~t) t` is a nonzero scalar
(`none` otherwise; Julia's general multivector algorithm is not ported here). -/
def invMetric? [Div α] (g : Gram α) (a : Multivector V α) : Option (Multivector V α) :=
  let d := abs2Metric g a
  let s := d.scalarValue
  let rest := (termsOf d).fold (fun ok B x => ok && (B == 0 || Coeff.isZero x)) true
  if rest && !Coeff.isZero s then some ((reverseTerms a).map (· / s)) else none

/-- Julia `/(a, b, g) = a ⟑ inv(b, g)` (`none` when `b` is not an invertible versor). -/
def divMetric? [Div α] (g : Gram α) (a b : Multivector V α) : Option (Multivector V α) :=
  (invMetric? g b).map (wedgedotMetric g a)

end Grassmann
