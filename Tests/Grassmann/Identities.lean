/-
`grassmann/identities`: classical geometric-algebra identities that `props` does not state,
over exact `Int` coefficients in the same spaces (`E2`-`E4`, `M4`, `PGA3`, `CGA3`, `DUAL3`):

* the involutions are involutions and commute, and `clifford = involute ∘ reverse`;
* the scalar part is a trace: `⟨ab⟩₀ = ⟨ba⟩₀` and `⟨abc⟩₀ = ⟨bca⟩₀`;
* `a = a₊ + a₋`, `(ab)₊ = a₊b₊ + a₋b₋`, `(ab)₋ = a₊b₋ + a₋b₊`, and `a = Σ_g ⟨a⟩_g`;
* the outer product is the antisymmetrised geometric product: `2 a∧b = ab - ba` and
  `6 a∧b∧c = Σ_σ sgn(σ) σ(a)σ(b)σ(c)` for vectors, in every metric (null and degenerate too);
* the commutator of two bivectors is a bivector, and `xB = x⋅B + x∧B` has only grades 1 and 3;
* the contraction is symmetric on vectors, the scalar product `⊛` is symmetric, and
  `x ⨼ (b ∧ c) = (x⋅b) c - (x⋅c) b` (left contraction derivation rule) for vectors;
* `antisandwich`: the pseudoscalar acts as the identity, and complements turn it into the
  ordinary sandwich, `antisandwich(⋆ˡR, ⋆ˡx) = ⋆ˡ(R >>> x)`;
* `pseudogradeProj G` is the grade-`(n - G)` projection.
-/
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors
open AbstractTensors (antisandwich pseudogradeProj)

namespace GrassmannTests.Identities

/-- Densify any element. -/
@[inline] def mv {X : Type} {V : TensorBundle} {α : Type} [AbstractTensors.Coeff α] [DenseLayout X V α]
    (x : X) : Multivector V α := toMultivector x

/-- The scalar part of a multivector. -/
def s0 {V : TensorBundle} (m : Multivector V Int) : Int := (m.grade 0).v.get! 0

/-- The multivector with only the grades in `gs` kept. -/
def keep {V : TensorBundle} (m : Multivector V Int) (gs : List Nat) : Multivector V Int :=
  gs.foldl (fun acc g => acc + mv (m.grade g)) 0

/-- The grade-`g` part of `m`, as a multivector. -/
def part {V : TensorBundle} (m : Multivector V Int) (g : Nat) : Multivector V Int := mv (m.grade g)

/-- Checks on general multivectors. -/
def mvIdentities (nm : String) (V : TensorBundle) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let a ← randMV V
    let b ← randMV V
    let c ← randMV V
    -- involutions
    t := t.check (~(~a) == a) s!"{nm}: ~~a ≠ a"
    t := t.check (involute (involute a) == a) s!"{nm}: involute² ≠ id"
    t := t.check (clifford (clifford a) == a) s!"{nm}: clifford² ≠ id"
    t := t.check (involute (~a) == ~(involute a)) s!"{nm}: involute and reverse do not commute"
    t := t.check (clifford a == involute (~a)) s!"{nm}: clifford ≠ involute ∘ reverse"
    -- the scalar part is a trace
    t := t.check (s0 (a * b) == s0 (b * a)) s!"{nm}: ⟨ab⟩₀ ≠ ⟨ba⟩₀"
    t := t.check (s0 (a * b * c) == s0 (b * c * a)) s!"{nm}: ⟨abc⟩₀ ≠ ⟨bca⟩₀"
    t := t.check (s0 (~a) == s0 a && s0 (involute a) == s0 a) s!"{nm}: involutions move ⟨a⟩₀"
    -- even and odd parts, grade decomposition
    let ev : Multivector V Int := mv (a₊)
    let od : Multivector V Int := mv (a₋)
    let evb : Multivector V Int := mv (b₊)
    let odb : Multivector V Int := mv (b₋)
    t := t.check (ev + od == a) s!"{nm}: a₊ + a₋ ≠ a"
    t := t.check (involute a == ev - od) s!"{nm}: involute a ≠ a₊ - a₋"
    t := t.check ((mv ((a * b)₊) : Multivector V Int) == ev * evb + od * odb) s!"{nm}: (ab)₊ ≠ a₊b₊ + a₋b₋"
    t := t.check ((mv ((a * b)₋) : Multivector V Int) == ev * odb + od * evb) s!"{nm}: (ab)₋ ≠ a₊b₋ + a₋b₊"
    t := t.check (keep a (List.range (V.n + 1)) == a) s!"{nm}: Σ_g ⟨a⟩_g ≠ a"
    -- the scalar product is symmetric
    t := t.check ((a ⊛ b : Chain V 0 Int) == (b ⊛ a : Chain V 0 Int)) s!"{nm}: a ⊛ b ≠ b ⊛ a"
  return t

/-- Checks on vectors and bivectors. -/
def vecIdentities (nm : String) (V : TensorBundle) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let a ← randChain V 1
    let b ← randChain V 1
    let c ← randChain V 1
    let x ← randChain V 1
    let A := mv a
    let B := mv b
    let C := mv c
    let X := mv x
    -- the outer product is the antisymmetrised geometric product
    t := t.check ((2 : Int) * mv (a ∧ b) == A * B - B * A) s!"{nm}: 2a∧b ≠ ab - ba"
    let alt : Multivector V Int :=
      A * B * C - A * C * B - B * A * C + B * C * A + C * A * B - C * B * A
    t := t.check ((6 : Int) * mv (a ∧ b ∧ c) == alt) s!"{nm}: 6a∧b∧c ≠ Σ sgn(σ) σ(abc)"
    -- contraction and scalar product of vectors are symmetric
    t := t.check (mv (a ⋅ b) == mv (b ⋅ a)) s!"{nm}: a⋅b ≠ b⋅a"
    -- left contraction derivation rule: x ⨼ (b∧c) = (x⋅b) c - (x⋅c) b
    let xb := s0 (mv (x ⋅ b))
    let xc := s0 (mv (x ⋅ c))
    t := t.check ((mv (x ⨼ (b ∧ c)) : Multivector V Int) == xb * C - xc * B)
      s!"{nm}: x ⨼ (b∧c) ≠ (x⋅b)c - (x⋅c)b"
    -- vector times bivector: grades 1 and 3 only, x⋅B + x∧B with the right contraction ⋅
    let Bv := b ∧ c
    let xBv := X * mv Bv
    t := t.check (keep xBv [1, 3] == xBv) s!"{nm}: x(b∧c) has grades other than 1, 3"
    t := t.check (part xBv 3 == mv (x ∧ Bv)) s!"{nm}: ⟨x(b∧c)⟩₃ ≠ x∧(b∧c)"
    -- the commutator of two bivectors is a bivector
    let D := mv (a ∧ x)
    let E := mv Bv
    let comm := D * E - E * D
    t := t.check (part comm 2 == comm) s!"{nm}: [B₁, B₂] is not a bivector"
  return t

/-- `antisandwich` and `pseudogradeProj` on chains of every grade. -/
def gradedIdentities (nm : String) (V : TensorBundle) : Tests.Gen Tally := do
  let mut t : Tally := {}
  let one : Chain V V.n Int := Chain.ofFn fun _ => 1
  for g in [0:V.n + 1] do
    let x ← randChain V g
    let r ← randChain V 2
    let tag := s!"{nm} grade {g}"
    -- the pseudoscalar `I` (with `!I = 1`) acts as the identity
    t := t.check (mv (antisandwich one x) == mv x) s!"{tag}: antisandwich(I, x) ≠ x"
    -- complements turn the antisandwich into the sandwich
    let lhs := mv (antisandwich (complementLeft r) (complementLeft x))
    let rhs := mv (complementLeft (r >>> x))
    t := t.check (lhs == rhs) s!"{tag}: antisandwich(⋆ˡR, ⋆ˡx) ≠ ⋆ˡ(R >>> x)"
  -- `pseudograde(t, G) = t(n - G)`
  for _ in [0:4] do
    let m ← randMV V
    t := t.check (mv (pseudogradeProj 0 m) == part m V.n) s!"{nm}: pseudograde 0 ≠ grade n"
    t := t.check (mv (pseudogradeProj 1 m) == part m (V.n - 1)) s!"{nm}: pseudograde 1 ≠ grade n-1"
  return t

/-- Run the identity suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let mut seed := 20261104
  for (nm, V) in spaces do
    seed := seed + 1
    t := t.merge (Tests.Gen.run seed (mvIdentities nm V 8))
    t := t.merge (Tests.Gen.run (seed + 500) (vecIdentities nm V 12))
    t := t.merge (Tests.Gen.run (seed + 900) (gradedIdentities nm V))
  return t

end GrassmannTests.Identities
