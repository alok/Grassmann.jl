import Clifford.Sparse

/-!
# `MultiGrade`: a multivector as its nonzero homogeneous parts

Julia `MultiGrade{V,G}` (Clifford.jl `src/multivectors.jl:68-149`, `src/algebra.jl:26-76`,
`src/products.jl`; port-notes/applied-misc.md §2.3, §4.3) stores the parts of a multivector
grade by grade, `G` being the bitmask of the grades present. Here the parts are a list in
ascending grade (each `Graded`, dense or sparse per `chainValues`) and the mask is derived from
it (`mask`), so the two can never disagree.

The intended semantics of port-notes §4.3 are implemented; the Julia defects are fixed:

* the involutions keep the `MultiGrade` structure (Julia returns a `SparseChain`);
* a complement maps grade `g` to `n - g` part by part, so the mask is *bit-reversed* over `n + 1`
  bits (Julia XORs it with `2ⁿ - 1`);
* `a - b` negates every part of `b` (Julia loses the sign of the second operand when the grades
  differ).
-/

namespace Clifford

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase

/-- Julia `MultiGrade{V,G}`: nonzero homogeneous parts in strictly ascending grade. -/
structure MultiGrade (V : TensorBundle) (α : Type) [Coeff α] where
  /-- the parts, ascending grades -/
  parts : List (Graded V α)

namespace MultiGrade

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- The empty multivector (zero). -/
def zero : MultiGrade V α := ⟨[]⟩

instance : Inhabited (MultiGrade V α) := ⟨zero⟩

/-- Julia's `G`: bit `g` set iff grade `g` is present. -/
def mask (m : MultiGrade V α) : UInt64 :=
  m.parts.foldl (fun acc p => acc ||| ((1 : UInt64) <<< p.grade.toUInt64)) 0

/-- The grades present, ascending. -/
def grades (m : MultiGrade V α) : List Nat := m.parts.map Graded.grade

/-- Julia `terms(m)`: the parts. -/
def terms (m : MultiGrade V α) : List (Graded V α) := m.parts

/-- Julia `value(m)`: the stored values of every part, concatenated. -/
def value (m : MultiGrade V α) : Array α := m.parts.foldl (fun acc p => acc ++ p.values) #[]

/-- The dense multivector: every part scattered at `binomsum(n, g) + index` (Julia's
`generate_sums` mixing with `MultiVector`). -/
def toMultivector (m : MultiGrade V α) : Multivector V α :=
  ⟨Values.ofFn fun i => m.parts.foldl (fun acc p => acc + getD p.toMultivector.v i.1) Coeff.zero⟩

/-- A part of grade `g` if nonzero. -/
def ofGraded (p : Graded V α) : MultiGrade V α := if p.isZero then zero else ⟨[p]⟩

/-- Julia `MultiGrade(::MultiVector)` (`src/multivectors.jl:88-96`): every nonzero grade as
`chainValues`. -/
def ofMultivector (m : Multivector V α) : MultiGrade V α :=
  ⟨(List.range (V.n + 1)).filterMap fun g =>
    let c := m.grade g
    if c.isZero then none else some (chainValues c)⟩

/-- A chain as a one-part `MultiGrade` (densified or sparsified by `chainValues`). -/
def ofChain {G : Nat} (c : Chain V G α) : MultiGrade V α := ofGraded (chainValues c)

/-- Two parts of the same grade combined with `f` on their dense chains, re-sparsified. -/
def combine (f : α → α → α) (p q : Graded V α) : Graded V α :=
  if h : q.grade = p.grade then chainValues (p.chain.zipWith f (q.chain.cast h))
  else p

/-- The two-pointer merge by ascending grade (`src/algebra.jl:26-52`), with `l`/`r` applied
to parts present on one side only and zero sums dropped. -/
def merge (l r : Graded V α → Graded V α) (f : α → α → α) (a b : MultiGrade V α) :
    MultiGrade V α :=
  ⟨go a.parts b.parts [] (a.parts.length + b.parts.length + 1)⟩
where
  /-- One step, fuelled by the total length; the result is built reversed. -/
  go : List (Graded V α) → List (Graded V α) → List (Graded V α) → Nat → List (Graded V α)
    | [], [], acc, _ => acc.reverse
    | _, _, acc, 0 => acc.reverse
    | p :: ps, [], acc, fuel + 1 => go ps [] (keep acc (l p)) fuel
    | [], q :: qs, acc, fuel + 1 => go [] qs (keep acc (r q)) fuel
    | p :: ps, q :: qs, acc, fuel + 1 =>
      if p.grade < q.grade then go ps (q :: qs) (keep acc (l p)) fuel
      else if q.grade < p.grade then go (p :: ps) qs (keep acc (r q)) fuel
      else go ps qs (keep acc (combine f p q)) fuel
  /-- Keep a part unless it is zero. -/
  keep (acc : List (Graded V α)) (p : Graded V α) : List (Graded V α) :=
    if p.isZero then acc else p :: acc

/-- A part mapped coefficientwise (sparsity recomputed). -/
def mapPart (f : α → α) (p : Graded V α) : Graded V α := chainValues (p.chain.map f)

/-- Julia `a + b` (`src/algebra.jl:26-52`): mask `A | B`. -/
def add (a b : MultiGrade V α) : MultiGrade V α := merge id id (· + ·) a b
/-- Julia `a - b`, every part of `b` negated. -/
def sub (a b : MultiGrade V α) : MultiGrade V α := merge id (mapPart (- ·)) (· - ·) a b
/-- Julia `-a` (keeping the `MultiGrade`). -/
def neg (a : MultiGrade V α) : MultiGrade V α := ⟨a.parts.map (mapPart (- ·))⟩
/-- Julia `x * a` (termwise, `src/products.jl:28-29`). -/
def smul (x : α) (a : MultiGrade V α) : MultiGrade V α :=
  ⟨(a.parts.map (mapPart (x * ·))).filter (fun p => not (Graded.isZero p))⟩

instance : Add (MultiGrade V α) := ⟨add⟩
instance : Sub (MultiGrade V α) := ⟨sub⟩
instance : Neg (MultiGrade V α) := ⟨neg⟩
instance : HMul α (MultiGrade V α) (MultiGrade V α) := ⟨smul⟩

/-- Julia `a ± t` for a homogeneous `t` of grade `B` (`src/algebra.jl:53-75`): added to the
grade-`B` part or inserted in order; mask `A | (1 << B)`. -/
def addChain {G : Nat} (a : MultiGrade V α) (c : Chain V G α) : MultiGrade V α := a + ofChain c

/-- Julia `a - t` for a homogeneous `t` (the sign of `t` kept). -/
def subChain {G : Nat} (a : MultiGrade V α) (c : Chain V G α) : MultiGrade V α := a - ofChain c

/-- Julia `scalar(m)`: the grade-0 coefficient (zero if absent). -/
def scalar (m : MultiGrade V α) : α :=
  match m.parts.find? (·.grade == 0) with
  | some p => (p.chain.v.toArray[0]?).getD Coeff.zero
  | none => Coeff.zero

/-- The grade-`g` part as a dense chain (zero if absent). -/
def part (m : MultiGrade V α) (g : Nat) : Chain V g α :=
  match m.parts.find? (·.grade == g) with
  | some p => if h : p.grade = g then p.chain.cast h else Chain.zero
  | none => Chain.zero

/-- Julia `vector(m)`: the grade-1 part (zero if absent). -/
def vector (m : MultiGrade V α) : Chain V 1 α := m.part 1

/-- Julia `volume(m)`: the grade-`n` part (zero if absent). -/
def volume (m : MultiGrade V α) : Chain V V.n α := m.part V.n

/-- Julia `isscalar(m)`: only the scalar grade is present (or nothing). -/
def isScalar (m : MultiGrade V α) : Bool := m.grades.all (· == 0)

/-- Julia `isvector(m)`: only grade 1 is present. -/
def isVector (m : MultiGrade V α) : Bool := m.grades == [1]

/-- Julia `==` (`src/multivectors.jl:61-64, 122`): the same coefficients grade by grade (a
missing grade counts as zero, so different masks compare equal only through zero parts). -/
def beq [BEq α] (a b : MultiGrade V α) : Bool := a.toMultivector == b.toMultivector

instance [BEq α] : BEq (MultiGrade V α) := ⟨beq⟩

variable [Kernels V]

/-- A type-preserving linear map applied part by part (the `MultiGrade` kept). -/
def unop (f : {g : Nat} → Chain V g α → Chain V g α) (m : MultiGrade V α) : MultiGrade V α :=
  ⟨(m.parts.map fun p => chainValues (f p.chain)).filter (fun p => not (Graded.isZero p))⟩

/-- Julia `reverse(m)` (`~m`), part by part. -/
def reverse (m : MultiGrade V α) : MultiGrade V α := unop Chain.reverse m
/-- Julia `involute(m)`. -/
def involute (m : MultiGrade V α) : MultiGrade V α := unop Chain.involute m
/-- Julia `conj(m)` (Grassmann's `clifford`). -/
def clifford (m : MultiGrade V α) : MultiGrade V α := unop Chain.clifford m

/-- A complement-type map part by part: grade `g ↦ n - g`, parts re-sorted ascending. -/
def comp (f : {g : Nat} → Chain V g α → Chain V (V.n - g) α) (m : MultiGrade V α) :
    MultiGrade V α :=
  ⟨((m.parts.map fun p => chainValues (f p.chain)).filter (fun p => not (Graded.isZero p))).reverse⟩

/-- Julia `complementright(m)` (`!m`). -/
def complementright (m : MultiGrade V α) : MultiGrade V α := comp Chain.complementright m
/-- Julia `complementleft(m)`. -/
def complementleft (m : MultiGrade V α) : MultiGrade V α := comp Chain.complementleft m

/-- The mask of a complement: bit `g` moves to bit `n - g` (a reversal over `n + 1` bits; Julia's
`G ⊻ (2ⁿ - 1)` is the defect). -/
def complementMask (n : Nat) (mask : UInt64) : UInt64 :=
  (List.range (n + 1)).foldl (fun acc g =>
    if (mask >>> g.toUInt64) &&& 1 == 1 then acc ||| ((1 : UInt64) <<< (n - g).toUInt64) else acc) 0

end MultiGrade

/-- Julia `MultiGrade(::MultiVector)` with its `fill_limit` rule (`src/multivectors.jl:88-96`):
the dense multivector itself when at most half of its coefficients are zero, else its
`MultiGrade`. -/
def compress {V : TensorBundle} {α : Type} [Coeff α] (m : Multivector V α) :
    Multivector V α ⊕ MultiGrade V α :=
  let zeros := m.v.toList.filter Coeff.isZero |>.length
  if (zeros : Rat) / ((2 ^ V.n : Nat) : Rat) < fillLimit then .inl m
  else .inr (MultiGrade.ofMultivector m)

/-! ## Display (`src/multivectors.jl:36-59, 98-105`) -/

section Show

variable {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `show(::SparseChain)`: the first nonzero value and its blade, then `" + " value` or
`" - " |value|` and the blade of each further one (compact values, as `Chain` prints them). -/
instance : ToString (SparseChain V G α) where
  toString s := if s.isZero then "0" else showTermsCompact V s.bladeTerms

/-- A part as Julia shows it (a dense part as a `Chain`). -/
def Graded.show : Graded V α → String
  | .dense _ c => toString c
  | .sparse _ s => toString s

/-- Julia `show(::MultiGrade)`: the parts joined by `" + "`, `0` when empty. -/
instance : ToString (MultiGrade V α) where
  toString m := if m.parts.isEmpty then "0" else " + ".intercalate (m.parts.map Graded.show)

end Show

end Clifford
