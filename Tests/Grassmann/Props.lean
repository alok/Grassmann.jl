/-
Algebraic property tests of the typed layer over exact `Int`/`Rat`
coefficients, in `E2`, `E3`, `E4`, `M4` (STA), `PGA3` (degenerate), `CGA3`
(conformal null basis), the dual space `DUAL3` and (for the products) the
tangent space `TAN2`:

* associativity and distributivity of `*`, `∧`, `∨`; `~(ab) = ~b ~a`,
  `involute` an automorphism, `clifford` an anti-automorphism;
* graded commutativity `a ∧ b = (-1)^{gh} b ∧ a`; `ab + ba = 2 a⋅b` and
  `ab = a⋅b + a∧b` for vectors; `a ∧ b = ⟨ab⟩_{g+h}`;
* complements: `complementleft ∘ ! = ! ∘ complementleft = id`,
  `!!x = (-1)^{g(n-g)} x`, `⋆⋆x = det(g)·(-1)^{g(n-g)} x`, `⋆x = (~x) I`,
  De Morgan `!(a ∨ b) = !a ∧ !b`;
* sandwiches with versors (`x ⊘ R`, `R >>> x`) equal the unprojected products;
* every typed result (chains, halves, all shape pairs) equals the
  `Multivector` product of the densified operands (the static result types never
  drop a contribution), and `inv` inverts vectors and rotors.
-/
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors

namespace GrassmannTests.Props

/-- Densify any element. -/
@[inline] def mv {X : Type} {V : TensorBundle} {α : Type} [AbstractTensors.Coeff α] [DenseLayout X V α]
    (x : X) : Multivector V α := toMultivector x

/-- The unit pseudoscalar `I = e_{1…n}` as a chain. -/
def pseudo (V : TensorBundle) : Chain V V.n Int := Chain.ofFn fun _ => 1

/-- `det g` of the space's Gram matrix, as an integer (`none` if not integral). -/
def detGram (V : TensorBundle) : Option Int :=
  let d := DirectSum.TensorBundle.ratDet V.gram
  if d.den == 1 then some d.num else none

/-- Properties of general multivectors (every space, tangent included). -/
def mvProps (nm : String) (V : TensorBundle) (tangent : Bool) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let a ← randMV V
    let b ← randMV V
    let c ← randMV V
    t := t.check ((a * b) * c == a * (b * c)) s!"{nm}: (ab)c ≠ a(bc)"
    t := t.check (a * (b + c) == a * b + a * c) s!"{nm}: a(b+c) ≠ ab + ac"
    t := t.check ((a + b) * c == a * c + b * c) s!"{nm}: (a+b)c ≠ ac + bc"
    t := t.check (~(a * b) == (~b) * (~a)) s!"{nm}: ~(ab) ≠ ~b ~a"
    t := t.check (involute (a * b) == involute a * involute b) s!"{nm}: involute not multiplicative"
    t := t.check (clifford (a * b) == clifford b * clifford a) s!"{nm}: clifford not an anti-automorphism"
    t := t.check ((((a ∧ b) ∧ c) : Multivector V Int) == (a ∧ (b ∧ c))) s!"{nm}: ∧ not associative"
    t := t.check ((2 : Int) * a == a + a) s!"{nm}: 2a ≠ a + a"
    t := t.check (a - a == 0) s!"{nm}: a - a ≠ 0"
    unless tangent do
      t := t.check ((((a ∨ b) ∨ c) : Multivector V Int) == (a ∨ (b ∨ c))) s!"{nm}: ∨ not associative"
      t := t.check (a.complementright.complementleft == a) s!"{nm}: complementleft ∘ ! ≠ id"
      t := t.check (a.complementleft.complementright == a) s!"{nm}: ! ∘ complementleft ≠ id"
      t := t.check ((!(a ∨ b) : Multivector V Int) == ((!a) ∧ (!b))) s!"{nm}: !(a∨b) ≠ !a ∧ !b"
      t := t.check ((⋆a : Multivector V Int) == (~a) * mv (pseudo V)) s!"{nm}: ⋆a ≠ (~a) I"
  return t

/-- Properties of chains and halves, for every pair of grades. -/
def gradedProps (nm : String) (V : TensorBundle) : Tests.Gen Tally := do
  let n := V.n
  let mut t : Tally := {}
  for g in [0:n + 1] do
    for h in [0:n + 1] do
      let x ← randChain V g
      let y ← randChain V h
      let z ← randChain V ((g + h) % (n + 1))
      let s ← randHalf V false
      let o ← randHalf V true
      let tag := s!"{nm} grades {g},{h}"
      -- typed results agree with the Multivector products of the densified operands
      t := t.check (mv (x * y) == mv x * mv y) s!"{tag}: typed * ≠ Multivector *"
      t := t.check (mv (x ∧ y) == (mv x ∧ mv y : Multivector V Int)) s!"{tag}: typed ∧"
      t := t.check (mv (x ∨ y) == (mv x ∨ mv y : Multivector V Int)) s!"{tag}: typed ∨"
      t := t.check (mv (x ⋅ y) == (mv x ⋅ mv y : Multivector V Int)) s!"{tag}: typed ⋅"
      t := t.check (mv (x * s) == mv x * mv s && mv (s * x) == mv s * mv x
        && mv (x * o) == mv x * mv o && mv (o * x) == mv o * mv x) s!"{tag}: typed chain×half *"
      t := t.check (mv (x ∧ s) == (mv x ∧ mv s : Multivector V Int) && mv (o ∧ x) == (mv o ∧ mv x : Multivector V Int))
        s!"{tag}: typed chain×half ∧"
      t := t.check (mv (x ∨ o) == (mv x ∨ mv o : Multivector V Int) && mv (s ∨ x) == (mv s ∨ mv x : Multivector V Int))
        s!"{tag}: typed chain×half ∨"
      t := t.check (mv (x ⋅ s) == (mv x ⋅ mv s : Multivector V Int) && mv (o ⋅ x) == (mv o ⋅ mv x : Multivector V Int))
        s!"{tag}: typed chain×half ⋅"
      -- associativity through the typed containers
      t := t.check (mv ((x * y) * z) == mv (x * (y * z))) s!"{tag}: typed (xy)z ≠ x(yz)"
      -- graded commutativity of ∧ and the grade projection of *
      t := t.check (mv (x ∧ y) == sgn (g * h) * mv (y ∧ x)) s!"{tag}: x∧y ≠ (-1)^gh y∧x"
      t := t.check ((x ∧ y) == gradePart (x * y) (g + h)) s!"{tag}: x∧y ≠ ⟨xy⟩_(g+h)"
      -- complements of a chain
      t := t.check (mv (!(!x)) == sgn (g * (n - g)) * mv x) s!"{tag}: !!x ≠ ±x"
      t := t.check (mv (x.complementright.complementleft) == mv x) s!"{tag}: complementleft(!x) ≠ x"
      if let some d := detGram V then
        t := t.check (mv (⋆(⋆x)) == (d * sgn (g * (n - g))) * mv x) s!"{tag}: ⋆⋆x ≠ det·(-1)^(g(n-g)) x"
      t := t.check (mv (⋆x) == mv ((~x) * pseudo V)) s!"{tag}: ⋆x ≠ (~x) I"
      -- involutions of a chain
      t := t.check (mv (~x) == sgn (g * (g - 1) / 2) * mv x) s!"{tag}: ~x sign"
      t := t.check (mv (involute x) == sgn g * mv x) s!"{tag}: involute sign"
      -- halves: products of the typed halves
      t := t.check (mv (s * o) == mv s * mv o && mv (o * o) == mv o * mv o) s!"{tag}: typed half×half *"
  -- vectors
  for _ in [0:4] do
    let a ← randChain V 1
    let b ← randChain V 1
    t := t.check (mv (a * b) == mv (a ⋅ b) + mv (a ∧ b)) s!"{nm}: ab ≠ a⋅b + a∧b"
    t := t.check (mv (a * b) + mv (b * a) == (2 : Int) * mv (a ⋅ b)) s!"{nm}: ab + ba ≠ 2 a⋅b"
    t := t.check (mv (a ∧ b) == -mv (b ∧ a)) s!"{nm}: a∧b ≠ -b∧a"
    -- versor actions with R = ab
    let x ← randChain V 1
    let R := a * b
    t := t.check (mv (x ⊘ R) == mv ((~R) * x * involute R)) s!"{nm}: x ⊘ R ≠ ~R x involute(R)"
    t := t.check (mv (R >>> x) == mv (R * x * clifford R)) s!"{nm}: R >>> x ≠ R x clifford(R)"
    t := t.check (mv (x ⊘ a) == mv ((~a) * x * involute a)) s!"{nm}: x ⊘ a"
  return t

/-- `inv` of vectors and rotors in the non-degenerate Euclidean spaces (over `Rat`). -/
def invProps (nm : String) (V : TensorBundle) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:6] do
    let a : Chain V 1 Rat := (← randChain V 1).map (fun (k : Int) => (k : Rat))
    let b : Chain V 1 Rat := (← randChain V 1).map (fun (k : Int) => (k : Rat))
    if !(a.abs2).isZero then
      t := t.check (mv (a * a⁻¹) == Multivector.one) s!"{nm}: a a⁻¹ ≠ 1"
    let R := a * b
    if !(scalarValue R.abs2 == 0) then
      match R.inv? with
      | some Ri => t := t.check (mv (R * Ri) == Multivector.one) s!"{nm}: R R⁻¹ ≠ 1"
      | none => t := t.bad s!"{nm}: rotor inverse undefined"
  return t

/-- `Submanifold V 1 * Submanifold V 1` is the `Couple` `g(eᵢ,eⱼ) + eᵢ∧eⱼ`. -/
def coupleProps (nm : String) (V : TensorBundle) : Tally := Id.run do
  let mut t : Tally := {}
  for i in [0:V.n] do
    for j in [0:V.n] do
      let a : Submanifold V 1 := ⟨Bits.bit (i + 1)⟩
      let b : Submanifold V 1 := ⟨Bits.bit (j + 1)⟩
      t := t.check ((a * b).toMultivector == mv a * mv b) s!"{nm}: e{i+1} e{j+1} as a Couple"
  return t

/-- Run the property suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let mut seed := 20260924
  for (nm, V) in spaces do
    seed := seed + 1
    t := t.merge (Tests.Gen.run seed (mvProps nm V false 6))
    t := t.merge (Tests.Gen.run (seed + 1000) (gradedProps nm V))
    t := t.merge (coupleProps nm V)
  for (nm, V) in [("E2", S!"++"), ("E3", S!"+++"), ("E4", S!"++++")] do
    t := t.merge (Tests.Gen.run (seed + 7) (invProps nm V))
  -- tangent space: products only (complements of tangent chains are not homogeneous)
  let tan2 := (S!"++").tangent 1 1
  t := t.merge (Tests.Gen.run 99 (mvProps "TAN2" tan2 true 6))
  return t

end GrassmannTests.Props
