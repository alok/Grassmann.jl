import AbstractAnalysis.Magma

/-!
# Permutations and cycles

Julia's `Permutation{N,T}` stores 1-based images `v[i] = σ(i)`, composes as
`(a*b)[i] = a[b[i]]` (b applied first) and inverts with `sortperm`
(src/perm.jl). The port stores the images 0-based as `Fin N` **together with
the inverse**, and carries the two inverse laws as (erased) proof fields.
That makes `inv` free, and the group axioms are short theorems
(`mul_assoc`, `one_mul`, `mul_one`, `inv_mul`, `mul_inv`), so `Perm N` is a
genuine group rather than a vector that happens to be a bijection.

Julia's `order(p)` is the transposition count (quirk #20); it is kept as
`transpositionCount`, and the true `groupOrder` (lcm of cycle lengths) is
provided alongside. Julia's `Cycle ==` ignores orientation (quirk #21):
`Julia.cycleEq` reproduces it, `Cycle.toPerm` equality is the correct notion.
-/

namespace AbstractAnalysis

/-- `Vector.get` of `Vector.ofFn`. -/
@[simp] theorem vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]; rfl

/-- A permutation of `Fin N` with its inverse (Julia `Permutation{N}`). -/
structure Perm (N : Nat) where
  /-- Images: `fwd[i] = σ(i)` (0-based). -/
  fwd : Vector (Fin N) N
  /-- Inverse images. -/
  bwd : Vector (Fin N) N
  /-- `σ⁻¹ ∘ σ = id`. -/
  bwd_fwd : ∀ i : Fin N, bwd.get (fwd.get i) = i
  /-- `σ ∘ σ⁻¹ = id`. -/
  fwd_bwd : ∀ i : Fin N, fwd.get (bwd.get i) = i

namespace Perm

variable {N : Nat}

/-- A permutation is determined by its images. -/
theorem ext {a b : Perm N} (h : a.fwd = b.fwd) : a = b := by
  have hb : a.bwd = b.bwd := by
    apply Vector.ext
    intro i hi
    have e1 := a.bwd_fwd (b.bwd.get ⟨i, hi⟩)
    rw [h, b.fwd_bwd ⟨i, hi⟩] at e1
    simpa [Vector.get] using e1
  cases a; cases b; simp_all

/-- Pointwise extensionality. -/
theorem fwd_ext {a b : Perm N} (h : ∀ i, a.fwd.get i = b.fwd.get i) : a = b :=
  ext (Vector.ext fun i hi => by simpa [Vector.get] using h ⟨i, hi⟩)

instance : DecidableEq (Perm N) := fun a b =>
  decidable_of_iff (a.fwd = b.fwd) ⟨ext, fun h => h ▸ rfl⟩

/-- Julia `Permutation{N}(I)`: the identity. -/
def one : Perm N := ⟨Vector.ofFn id, Vector.ofFn id, by simp, by simp⟩

/-- Julia `a * b = a(b)`: `(a*b)(i) = a(b(i))`, `b` applied first. -/
def mul (a b : Perm N) : Perm N :=
  ⟨Vector.ofFn fun i => a.fwd.get (b.fwd.get i), Vector.ofFn fun i => b.bwd.get (a.bwd.get i),
   by intro i; simp [a.bwd_fwd, b.bwd_fwd], by intro i; simp [a.fwd_bwd, b.fwd_bwd]⟩

/-- Julia `inv(p)` (`sortperm`): here just the stored inverse. -/
def inv (a : Perm N) : Perm N := ⟨a.bwd, a.fwd, a.fwd_bwd, a.bwd_fwd⟩

instance : Mul (Perm N) := ⟨mul⟩
instance : Inv (Perm N) := ⟨inv⟩
instance : OfNat (Perm N) 1 := ⟨one⟩
instance : Inhabited (Perm N) := ⟨one⟩

@[simp] theorem mul_fwd (a b : Perm N) (i : Fin N) : (a * b).fwd.get i = a.fwd.get (b.fwd.get i) := by
  simp [HMul.hMul, Mul.mul, mul]

@[simp] theorem one_fwd (i : Fin N) : (1 : Perm N).fwd.get i = i := by
  simp [OfNat.ofNat, one]

@[simp] theorem inv_fwd (a : Perm N) (i : Fin N) : a⁻¹.fwd.get i = a.bwd.get i := rfl

/-- Composition is associative. -/
theorem mul_assoc (a b c : Perm N) : a * b * c = a * (b * c) := fwd_ext fun _ => by simp

/-- The identity is a left unit. -/
theorem one_mul (a : Perm N) : 1 * a = a := fwd_ext fun _ => by simp

/-- The identity is a right unit. -/
theorem mul_one (a : Perm N) : a * 1 = a := fwd_ext fun _ => by simp

/-- `a⁻¹ a = 1`. -/
theorem inv_mul (a : Perm N) : a⁻¹ * a = 1 := fwd_ext fun _ => by simp [a.bwd_fwd]

/-- `a a⁻¹ = 1`. -/
theorem mul_inv (a : Perm N) : a * a⁻¹ = 1 := fwd_ext fun _ => by simp [a.fwd_bwd]

/-- Invert an image vector (`O(N)`). -/
def invertImages (f : Vector (Fin N) N) : Vector (Fin N) N :=
  (List.finRange N).foldl (fun acc i => acc.set (f.get i) i) (Vector.ofFn id)

/-- Build from 0-based images, checking bijectivity. -/
def ofFwd? (f : Vector (Fin N) N) : Option (Perm N) :=
  let b := invertImages f
  if h1 : ∀ i : Fin N, b.get (f.get i) = i then
    if h2 : ∀ i : Fin N, f.get (b.get i) = i then some ⟨f, b, h1, h2⟩ else none
  else none

/-- Julia `Permutation(v...)`: from 1-based images, if they form a permutation. -/
def ofList? (l : List Nat) : Option (Perm N) :=
  if h : l.length = N then
    if hv : l.all (fun k => 1 ≤ k && k ≤ N) then
      ofFwd? (Vector.ofFn fun i : Fin N =>
        ⟨l[i.1]'(h ▸ i.2) - 1, by
          have := List.all_eq_true.mp hv (l[i.1]'(h ▸ i.2)) (List.getElem_mem _)
          simp at this; omega⟩)
    else none
  else none

/-- `ofList?` for trusted input (identity on failure). -/
def ofList! (l : List Nat) : Perm N := (ofList? l).getD one

/-- 1-based images, as Julia prints them. -/
def toList (p : Perm N) : List Nat := p.fwd.toList.map (·.1 + 1)

/-- Julia `p[i]` / `p(i)` (1-based; identity outside `1..N`). -/
def apply (p : Perm N) (i : Nat) : Nat := if h : 0 < i ∧ i ≤ N then (p.fwd.get ⟨i - 1, by omega⟩).1 + 1 else i

/-- Julia `a / b = a(inv b)`. -/
def div (a b : Perm N) : Perm N := a * b⁻¹

/-- Julia `a \ b = inv(a)(b)`. -/
def ldiv (a b : Perm N) : Perm N := a⁻¹ * b

/-- Natural powers. -/
def npow (a : Perm N) : Nat → Perm N
  | 0 => 1
  | k + 1 => a * npow a k

/-- Julia `a ^ n` for any integer `n` (negative powers invert). -/
def zpow (a : Perm N) (n : Int) : Perm N :=
  if n ≥ 0 then npow a n.toNat else npow a⁻¹ n.natAbs

instance : HPow (Perm N) Int (Perm N) := ⟨zpow⟩

/-! ## Cycles -/

/-- The cycle through `i`: `i, p(i), p²(i), …` (Julia `getcycle`). -/
def orbitOf (p : Perm N) (i : Fin N) : List (Fin N) :=
  go [i] (p.fwd.get i) N
where
  /-- Follow `p` until the orbit closes. -/
  go (acc : List (Fin N)) (j : Fin N) : Nat → List (Fin N)
    | 0 => acc.reverse
    | fuel + 1 => if acc.contains j then acc.reverse else go (j :: acc) (p.fwd.get j) fuel

/-- Julia `CycleProduct(p)`: the nontrivial disjoint cycles, each started at its
smallest element, in order of that element (src/perm.jl:84-93). -/
def cycles (p : Perm N) : List (List (Fin N)) :=
  ((List.finRange N).foldl (fun (acc : List (List (Fin N))) i =>
    if acc.any (·.contains i) then acc
    else let c := p.orbitOf i; if c.length == 1 then acc else c :: acc) []).reverse

/-- Julia `order(p)`: **the transposition count** `Σ (|c| - 1)`, not the group
order (quirk #20). -/
def transpositionCount (p : Perm N) : Nat := (p.cycles.map (·.length - 1)).foldl (· + ·) 0

/-- Julia `levicivita(p)` / `ε(p)`: the sign `(-1)^transpositionCount`. -/
def sign (p : Perm N) : Int := if p.transpositionCount % 2 = 0 then 1 else -1

/-- Julia `iseven(p)`. -/
def isEven (p : Perm N) : Bool := p.transpositionCount % 2 = 0

/-- Julia `isodd(p) = isodd(order(p))` (src/perm.jl:21). -/
def isOdd (p : Perm N) : Bool := p.transpositionCount % 2 = 1

/-- The element commutator `g⁻¹ h⁻¹ g h`. Julia's `commutator(g, h) = commutator(group(g),
group(h))` (src/perm.jl:51) passes the permutations' image vectors as generators (a
permutation is an `AbstractVector{Int}`), so it is broken; this is the intended element. -/
def commutator (g h : Perm N) : Perm N := g⁻¹ * h⁻¹ * g * h

/-- The true order of `p` in the group: the lcm of its cycle lengths. -/
def groupOrder (p : Perm N) : Nat := (p.cycles.map List.length).foldl Nat.lcm 1

/-- Display as Julia does: 1-based images `[2, 3, 1]`. -/
instance : JuliaRepr (Perm N) :=
  ⟨fun p => JuliaRepr.repr p.toList.toArray, fun p => JuliaRepr.repr p.toList.toArray, false⟩

instance : ApproxEq (Perm N) := ⟨(· == ·)⟩

instance : HasParity (Perm N) := ⟨isEven⟩

/-- The permutation group law (`*`, `inv`). -/
abbrev law (N : Nat) : Law (Perm N) := ⟨(· * ·), Perm.inv⟩

end Perm

/-- Julia `Cycle{N}`: a cycle `a₁ → a₂ → … → aₖ → a₁` (0-based entries). -/
structure Cycle (N : Nat) where
  /-- The cycle list. -/
  v : List (Fin N)
  deriving DecidableEq

namespace Cycle

variable {N : Nat}

/-- Julia `evalperm(c, i)` (src/perm.jl:63-66). -/
def eval (c : Cycle N) (i : Fin N) : Fin N :=
  match c.v.idxOf? i with
  | none => i
  | some j => if j + 1 = c.v.length then c.v.head?.getD i else c.v[j + 1]?.getD i

/-- Julia `Permutation(c::Cycle)` (identity if the list repeats an entry). -/
def toPerm (c : Cycle N) : Perm N := (Perm.ofFwd? (Vector.ofFn c.eval)).getD 1

/-- Julia `Cycle{N}(n...)` from 1-based entries. -/
def ofList (l : List Nat) : Cycle N :=
  ⟨l.filterMap fun k => if h : 0 < k ∧ k ≤ N then some ⟨k - 1, by omega⟩ else none⟩

/-- 1-based entries. -/
def toList (c : Cycle N) : List Nat := c.v.map (·.1 + 1)

/-- Julia `order(::Cycle) = length - 1`. -/
def transpositionCount (c : Cycle N) : Nat := c.v.length - 1

/-- Julia `isdisjoint(a, b)`: no shared entries. -/
def isDisjoint (a b : Cycle N) : Bool := a.v.all fun x => !b.v.contains x

/-- Julia `isabelian(a, b)` (src/perm.jl:118): whether the cycles commute. Julia tests the
condition `isdisjoint(a, b) || a == b` with the quirk-#21 `==` (same entry set): that accepts
`(1,2,3)` with its inverse `(1,3,2)` (correctly, by luck) but also `(1,2,3,4)` with `(1,2,4,3)`,
which do not commute (see `Julia.cycleIsAbelian`); this decides commutation exactly. -/
def isAbelian (a b : Cycle N) : Bool := a.isDisjoint b || a.toPerm * b.toPerm == b.toPerm * a.toPerm

/-- Julia `levicivita(c) = isodd(c) ? -1 : 1`. -/
def sign (c : Cycle N) : Int := if c.transpositionCount % 2 = 0 then 1 else -1

/-- Julia `iseven(c) = iseven(order(c))` (src/perm.jl:22): an odd-length cycle. -/
def isEven (c : Cycle N) : Bool := c.transpositionCount % 2 = 0

/-- Julia `isodd(c) = isodd(order(c))` (src/perm.jl:21): an even-length cycle. -/
def isOdd (c : Cycle N) : Bool := c.transpositionCount % 2 = 1

/-- Display as Julia shows a cycle (an `AbstractVector{Int}`): `[1, 2, 3]`. -/
instance : JuliaRepr (Cycle N) :=
  ⟨fun c => JuliaRepr.repr c.toList.toArray, fun c => JuliaRepr.repr c.toList.toArray, false⟩

end Cycle

/-- Julia `Transposition{N} = Cycle{N,Values{2,Int}}` (src/perm.jl:58): a 2-cycle. -/
abbrev Transposition (N : Nat) := {c : Cycle N // c.v.length = 2}

/-- The transposition of the 1-based entries `a ≠ b`. -/
def Transposition.mk? {N : Nat} (a b : Nat) : Option (Transposition N) :=
  let c : Cycle N := Cycle.ofList [a, b]
  if h : c.v.length = 2 then if a != b then some ⟨c, h⟩ else none else none

/-- Julia `CycleProduct{N}`: a product of cycles, the rightmost applied first (src/perm.jl:71-80). -/
structure CycleProduct (N : Nat) where
  /-- The cycles. -/
  cycles : List (Cycle N)
  deriving DecidableEq

/-- Julia `Permutation(c::CycleProduct)`: the product with the rightmost cycle
applied first (identity for the empty product). -/
def cycleProduct {N : Nat} (cs : List (Cycle N)) : Perm N := cs.foldl (fun acc c => acc * c.toPerm) 1

namespace CycleProduct

variable {N : Nat}

/-- Julia `Permutation(c::CycleProduct)`. -/
def toPerm (c : CycleProduct N) : Perm N := cycleProduct c.cycles

/-- Julia `order(c::CycleProduct)`: the transposition count, `Σ (|cᵢ| - 1)` (src/perm.jl:109). -/
def transpositionCount (c : CycleProduct N) : Nat := (c.cycles.map Cycle.transpositionCount).foldl (· + ·) 0

/-- Julia `levicivita(c) = prod(levicivita.(c.v))`. -/
def sign (c : CycleProduct N) : Int := (c.cycles.map Cycle.sign).foldl (· * ·) 1

/-- Julia's display: a `CycleProduct` is an `AbstractVector{Int}` whose entries are cycles,
so it shows as `[[1, 2], [3, 4]]`, and the empty product as `Int64[]`. -/
def repr (c : CycleProduct N) : String :=
  if c.cycles.isEmpty then "Int64[]"
  else "[" ++ ", ".intercalate (c.cycles.map fun x => JuliaRepr.repr x) ++ "]"

instance : JuliaRepr (CycleProduct N) := ⟨repr, repr, false⟩

end CycleProduct

/-- Julia `CycleProduct(p)` (src/perm.jl:84-93): the nontrivial disjoint cycles, each from its
smallest element, in order of that element. -/
def Perm.cycleProductOf {N : Nat} (p : Perm N) : CycleProduct N := ⟨p.cycles.map (⟨·⟩)⟩

/-- Julia `decompose(p)` (src/perm.jl:94-97): the single `Cycle` when `p` has exactly one
nontrivial cycle, the `CycleProduct` otherwise. -/
def Perm.decompose {N : Nat} (p : Perm N) : Cycle N ⊕ CycleProduct N :=
  match p.cycles with
  | [c] => .inl ⟨c⟩
  | cs => .inr ⟨cs.map (⟨·⟩)⟩

/-- Julia's display of a `decompose` result. -/
def decomposeRepr {N : Nat} : Cycle N ⊕ CycleProduct N → String
  | .inl c => JuliaRepr.repr c
  | .inr c => JuliaRepr.repr c

/-- Julia `decompose(G::Semimagma) = Semimagma(decompose.(G.v))` (src/perm.jl:103). -/
def Semimagma.decompose {N : Nat} {L : Law (Perm N)} (G : Semimagma (Perm N) L) :
    Array (Cycle N ⊕ CycleProduct N) :=
  G.v.map Perm.decompose

/-- Julia `Cycle ==` as written (**quirk #21**): equal lengths and the same
entry set, so `(1,2,3) == (1,3,2)`. -/
def Julia.cycleEq {N : Nat} (a b : Cycle N) : Bool := a.v.length == b.v.length && a.v.all b.v.contains

/-- Julia `isabelian(a, b) = isdisjoint(a, b) || a == b` as written, with the quirk-#21 `==`:
`(1,2,3,4)` and `(1,2,4,3)` count as commuting although they do not (`Cycle.isAbelian` decides
commutation). -/
def Julia.cycleIsAbelian {N : Nat} (a b : Cycle N) : Bool := a.isDisjoint b || Julia.cycleEq a b

/-! ## Standard permutation groups -/

/-- Lexicographic permutations of a sorted list (Combinatorics' order). -/
def lexPermutations : List Nat → Nat → List (List Nat)
  | [], _ => [[]]
  | _, 0 => []
  | l, fuel + 1 => l.flatMap fun x => (lexPermutations (l.erase x) fuel).map (x :: ·)

/-- Julia `SymmetricGroup(N)`: all permutations in lexicographic order. -/
def SymmetricGroup (N : Nat) : Semimagma (Perm N) (Perm.law N) :=
  ⟨((lexPermutations ((List.range N).map (· + 1)) N).map Perm.ofList!).toArray⟩

/-- Julia `AlternatingGroup(N)`: the even permutations, order preserved. -/
def AlternatingGroup (N : Nat) : Semimagma (Perm N) (Perm.law N) :=
  ⟨(SymmetricGroup N).v.filter Perm.isEven⟩

/-- Julia `DihedralGroup(r, s)` as intended: `group([s]) * group([r])`, the
products `sⁱ rʲ` (Julia's own method is broken, quirk #19). -/
def DihedralGroup {N : Nat} (r s : Perm N) : Semimagma (Perm N) (Perm.law N) :=
  Semimagma.compose (Semimagma.group #[s]) (Semimagma.group #[r])

/-! ## Kernel-checked tables

The whole pipeline (lexicographic generation, composition, cycle
decomposition, the Julia predicates) reduces in the kernel, so small groups are
verified outright rather than sampled. -/

/-- `levicivita` is a homomorphism on `S₃` (all 36 pairs). -/
theorem sign_mul_S3 : ∀ a ∈ (SymmetricGroup 3).v.toList, ∀ b ∈ (SymmetricGroup 3).v.toList,
    (a * b).sign = a.sign * b.sign := by decide +kernel

/-- `levicivita` is a homomorphism on `S₄` (all 576 pairs). -/
theorem sign_mul_S4 : ∀ a ∈ (SymmetricGroup 4).v.toList, ∀ b ∈ (SymmetricGroup 4).v.toList,
    (a * b).sign = a.sign * b.sign := by decide +kernel

/-- Julia's `isgroup(S₃)` holds (closure, associativity, inverses). -/
theorem S3_isGroup : Semimagma.isGroup (SymmetricGroup 3) = true := by decide +kernel

/-- `S₃` is the smallest nonabelian group. -/
theorem S3_nonabelian : Semimagma.isAbelian (SymmetricGroup 3) = false := by decide +kernel

/-- `|A₄| = 12`. -/
theorem A4_card : (AlternatingGroup 4).v.size = 12 := by decide +kernel

/-- The alternating group is Julia's `commutator(S₃)` (as sets). -/
theorem commutator_S3 : Semimagma.setEq (Semimagma.commutator (SymmetricGroup 3) (SymmetricGroup 3))
    (AlternatingGroup 3) = true := by decide +kernel

end AbstractAnalysis
