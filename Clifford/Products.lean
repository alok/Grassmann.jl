import Clifford.MultiGrade
import Std.Data.HashMap

/-!
# Sparse products of `MultiGrade`

Clifford.jl never implemented products (port-notes/applied-misc.md §4.3: "everything else
(products) was never implemented"). Here they are the bilinear extension of DirectSum's
blade-level rules (`TensorBundle.terms₂`), the same rules the dense reference kernels of
`Grassmann.Kernel` interpret, but evaluated only on the stored (nonzero) terms:

  `op(a, b) = Σ_{(A, x) ∈ a} Σ_{(B, y) ∈ b} Σ_{(C, c) ∈ op(e_A, e_B)} c·x·y e_C`

so a product of elements with `p` and `q` nonzero terms costs `O(p·q)` blade evaluations
whatever `2ⁿ` is. That is the point of sparse storage: in `ℝ^16` a product of two vectors with
three terms each touches 9 blade pairs, where a dense `Multivector` has 65536 coefficients.
Every result part is re-stored by the `chainvalues` densify rule (`chainValues`), and the
dense containers are the reference (`toMultivector` is a homomorphism for every product,
`Tests.Clifford`).

The products provided are the total ones: geometric `*`, exterior `∧`, regressive `∨`, the
(right) contraction `⋅` and the left contraction `⨼`. Contributions carrying a repeated
tangent generator (DirectSum's `z ≠ 0`) are dropped, as the dense kernels drop them
(`Plan.nested`).
-/

namespace Clifford

open Grassmann DirectSum StaticVectors AbstractTensors

namespace MultiGrade

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- The `(blade, value)` terms of a part (nonzero values only), in storage order. -/
def Graded.bladeTerms : Graded V α → List (UInt64 × α)
  | .sparse _ s => s.bladeTerms
  | .dense g c =>
    (c.v.toList.zipIdx.filter fun (x, _) => !Coeff.isZero x).map fun (x, i) =>
      (Leibniz.unrank V.n g i, x)

/-- Every nonzero `(blade, value)` term, ascending grade then storage order. -/
def bladeTerms (m : MultiGrade V α) : List (UInt64 × α) := m.parts.flatMap Graded.bladeTerms

/-- A part of grade `g` from its nonzero `(index, value)` terms (indices strictly increasing),
stored by the `chainvalues` rule without densifying a part that stays sparse. -/
def partOfTerms (g : Nat) (ts : Array (Nat × α)) : Graded V α :=
  let size := Leibniz.binomial V.n g
  let zeros := size - ts.size
  let s : SparseChain V g α := ⟨ts⟩
  if g == 0 || g == V.n || (zeros : Rat) / (max size 1 : Nat) < fillLimit then .dense g s.toChain
  else .sparse g s

/-- The `MultiGrade` of a blade ↦ value map (zero values dropped). -/
def ofBladeMap (m : Std.HashMap UInt64 α) : MultiGrade V α := Id.run do
  let mut byGrade : Array (Array (Nat × α)) := Array.replicate (V.n + 1) #[]
  for (b, x) in m.toList do
    if !Coeff.isZero x then
      let g := DirectSum.Bits.popcount b
      if g ≤ V.n then
        byGrade := byGrade.modify g (·.push (Leibniz.bladeRank V.n b, x))
  let mut parts : List (Graded V α) := []
  for g in (List.range (V.n + 1)).reverse do
    let ts := byGrade[g]!.qsort (fun p q => p.1 < q.1)
    if !ts.isEmpty then parts := partOfTerms g ts :: parts
  return ⟨parts⟩

/-- The coefficient `c·x·y` of one contribution, without a multiplication for `c = ±1`. -/
@[inline] def scaled (c : Rat) (x y : α) : α :=
  if c == 1 then x * y else if c == -1 then -(x * y) else Coeff.ofRat c * (x * y)

/-- The sparse bilinear extension of the blade operation `op`: every pair of stored terms,
accumulated by blade. Pairs on which the blade rule fails (complements in a dyadic space) and
nested tangent contributions are dropped. -/
def binop (op : BinOp) (a b : MultiGrade V α) : MultiGrade V α := Id.run do
  let bs := b.bladeTerms
  let mut acc : Std.HashMap UInt64 α := {}
  for (A, x) in a.bladeTerms do
    for (B, y) in bs do
      match V.terms₂ op A B with
      | .ok ts =>
        for t in ts do
          if t.z == 0 then
            acc := acc.insert t.bits (acc.getD t.bits Coeff.zero + scaled t.coef x y)
      | .error _ => pure ()
  return ofBladeMap acc

/-- The geometric product. -/
def mul (a b : MultiGrade V α) : MultiGrade V α := binop .mul a b
/-- The exterior product `a ∧ b`. -/
def wedge (a b : MultiGrade V α) : MultiGrade V α := binop .wedge a b
/-- The regressive product `a ∨ b`. -/
def vee (a b : MultiGrade V α) : MultiGrade V α := binop .vee a b
/-- The (right) contraction `a ⋅ b` (Julia `contraction`, `⨽`). -/
def contraction (a b : MultiGrade V α) : MultiGrade V α := binop .contraction a b
/-- The left contraction `a ⨼ b = contraction(b, a)`. -/
def contractionLeft (a b : MultiGrade V α) : MultiGrade V α := binop .contractionLeft a b

instance : Mul (MultiGrade V α) := ⟨mul⟩
instance : Wedge (MultiGrade V α) (MultiGrade V α) (MultiGrade V α) := ⟨wedge⟩
instance : Vee (MultiGrade V α) (MultiGrade V α) (MultiGrade V α) := ⟨vee⟩
instance : Contraction (MultiGrade V α) (MultiGrade V α) (MultiGrade V α) := ⟨contraction⟩

/-- A single term `x e_B`. -/
def term (B : UInt64) (x : α) : MultiGrade V α := ofBladeMap ((({} : Std.HashMap UInt64 α)).insert B x)

/-- The number of stored nonzero coefficients. -/
def nnz (m : MultiGrade V α) : Nat := m.bladeTerms.length

end MultiGrade

end Clifford
