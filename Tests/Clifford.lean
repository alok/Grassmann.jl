import Clifford
import Tests.Util.Random

/-!
Clifford tests. Julia's Clifford.jl never loads (port-notes/applied-misc.md §1.3), so there is no
oracle: the sparse containers are checked against Grassmann's dense ones, which are themselves
oracle-tested. For random `Int` elements of ℝ3, ℝ4 and ℝ5, `toMultivector` is a homomorphism for
`+ - *` (scalar), negation, the involutions and the complements; the densify rule, the masks
(including the bit-reversed complement mask), the accessors and the printed forms are checked
on explicit examples.
-/

namespace Tests.Clifford

open Grassmann _root_.Clifford DirectSum StaticVectors AbstractTensors

/-! ## Explicit examples (compile time) -/

/-- `1v₁ - 2v₃` in ℝ3. -/
def s1 : SparseChain ℝ3 1 Int := SparseChain.ofTerms [(0b001, 1), (0b100, -2)]
/-- `3v₂ + 2v₃`. -/
def s2 : SparseChain ℝ3 1 Int := SparseChain.ofTerms [(0b010, 3), (0b100, 2)]

#guard toString s1 == "1v₁ - 2v₃"
#guard (s1 + s2).terms == #[(0, 1), (1, 3)]
#guard (s1 - s2).terms == #[(0, 1), (1, -3), (2, -4)]
#guard (-s1).terms == #[(0, -1), (2, 2)]
#guard ((3 : Int) * s1).terms == #[(0, 3), (2, -6)]
#guard toString (SparseChain.zero : SparseChain ℝ3 2 Int) == "0"
-- `Term - SparseChain` keeps the sign of the chain (Julia's `b + a` bug)
#guard (SparseChain.singleSub (⟨0b001, 5⟩ : Single ℝ3 1 Int) s1).terms == #[(0, 4), (2, 2)]
-- the densify rule: ℝ4 grade 2 has 6 blades; one nonzero is sparse, four are dense
#guard (chainValues ((SparseChain.ofTerms [(0b0011, (1 : Int))] : SparseChain ℝ4 2 Int).toChain)).isSparse
#guard !(chainValues ((SparseChain.ofTerms [(0b0011, (1 : Int)), (0b0101, 2), (0b0110, 3),
  (0b1001, 4)] : SparseChain ℝ4 2 Int).toChain)).isSparse
-- exactly half zeros is sparse; the scalar and pseudoscalar grades are always dense
#guard (chainValues ((SparseChain.ofTerms [(0b0011, (1 : Int)), (0b0101, 2), (0b0110, 3)] :
  SparseChain ℝ4 2 Int).toChain)).isSparse
#guard !(chainValues (Chain.scalar (0 : Int) : Chain ℝ4 0 Int)).isSparse
-- masks: `1 + v₁₂₃` in ℝ3 has grades {0, 3}; its complement has grades {3, 0} (bit-reversed)
def mg : MultiGrade ℝ3 Int :=
  MultiGrade.ofChain (Chain.scalar (1 : Int) : Chain ℝ3 0 Int) +
    MultiGrade.ofChain ((SparseChain.ofTerms [(0b111, (1 : Int))] : SparseChain ℝ3 3 Int).toChain)
#guard mg.mask == 0b1001
#guard MultiGrade.complementMask 3 0b0011 == 0b1100
#guard (MultiGrade.ofChain s1.toChain).complementright.mask ==
  MultiGrade.complementMask 3 (MultiGrade.ofChain s1.toChain).mask
#guard mg.scalar == 1 && mg.volume.v.toList == [1] && !mg.isVector && !mg.isScalar
#guard (MultiGrade.ofChain s1.toChain).isVector && (MultiGrade.ofChain s1.toChain).vector.v.toList == [1, 0, -2]
#guard toString mg == "1v + 1v₁₂₃"
#guard toString (MultiGrade.zero : MultiGrade ℝ3 Int) == "0"
#guard (mg - mg).parts.isEmpty

/-! ## Randomised homomorphism checks -/

/-- A random `Int` chain of grade `G` with about `density`/8 of its entries nonzero. -/
def randChain (V : TensorBundle) (G : Nat) (density : Nat) (g : Tests.Rng) : Chain V G Int × Tests.Rng :=
  Id.run do
    let mut g := g
    let mut xs : Array Int := #[]
    for _ in [0:Leibniz.binomial V.n G] do
      let (u, g') := g.next
      g := g'
      let keep := (u % 8).toNat < density
      let v : Int := ((u >>> 8) % 11).toNat - 5
      xs := xs.push (if keep then v else 0)
    return ((Chain.ofArray? xs).getD Chain.zero, g)

/-- A random `MultiGrade` over every grade of `V`. -/
def randMulti (V : TensorBundle) [Kernels V] (g : Tests.Rng) : MultiGrade V Int × Tests.Rng := Id.run do
  let mut g := g
  let mut m : MultiGrade V Int := MultiGrade.zero
  for k in [0:V.n + 1] do
    let (d, g1) := g.next
    let (c, g2) := randChain V k (d % 9).toNat g1
    g := g2
    m := m + MultiGrade.ofChain c
  return (m, g)

/-- The homomorphism properties in space `V`. -/
def props (V : TensorBundle) [Kernels V] (name : String) (seed : Nat) :
    List (String × Bool) := Id.run do
  let mut g := Tests.Rng.ofSeed seed
  let mut ok : Array (String × Bool) := #[]
  let mut sum := true
  let mut diff := true
  let mut negOk := true
  let mut scal := true
  let mut rev := true
  let mut inv := true
  let mut cl := true
  let mut cr := true
  let mut cleft := true
  let mut sorted := true
  let mut roundtrip := true
  let mut sparseOps := true
  for _ in [0:60] do
    let (a, g1) := randMulti V g
    let (b, g2) := randMulti V g1
    let (x, g3) := g2.next
    g := g3
    let k : Int := (x % 7).toNat - 3
    let A := a.toMultivector
    let B := b.toMultivector
    if !((a + b).toMultivector == A + B) then sum := false
    if !((a - b).toMultivector == A - B) then diff := false
    if !((-a).toMultivector == -A) then negOk := false
    if !((k * a).toMultivector == Multivector.map (k * ·) A) then scal := false
    if !(a.reverse.toMultivector == A.reverse) then rev := false
    if !(a.involute.toMultivector == A.involute) then inv := false
    if !(a.clifford.toMultivector == A.clifford) then cl := false
    if !(a.complementright.toMultivector == A.complementright) then cr := false
    if !(a.complementleft.toMultivector == A.complementleft) then cleft := false
    let gs := (a + b).grades
    if !(gs == (gs.toArray.qsort (· < ·)).toList && gs.eraseDups == gs) then sorted := false
    if !((MultiGrade.ofMultivector A).toMultivector == A) then roundtrip := false
    -- sparse chains of grade 2 alone
    let (c, g4) := randChain V 2 3 g
    let (d, g5) := randChain V 2 3 g4
    g := g5
    let sc := SparseChain.ofChain c
    let sd := SparseChain.ofChain d
    if !((sc + sd).toChain == Chain.zipWith (· + ·) c d && (sc - sd).toChain == Chain.zipWith (· - ·) c d &&
        sc.reverse.toChain == c.reverse && sc.complementright.toChain == c.complementright &&
        sc.toMultivector == Grassmann.toMultivector c) then sparseOps := false
  ok := ok.push (s!"{name}: (a + b)♯ = a♯ + b♯", sum)
  ok := ok.push (s!"{name}: (a - b)♯ = a♯ - b♯", diff)
  ok := ok.push (s!"{name}: (-a)♯ = -a♯", negOk)
  ok := ok.push (s!"{name}: (k a)♯ = k a♯", scal)
  ok := ok.push (s!"{name}: reverse", rev)
  ok := ok.push (s!"{name}: involute", inv)
  ok := ok.push (s!"{name}: clifford", cl)
  ok := ok.push (s!"{name}: complementright", cr)
  ok := ok.push (s!"{name}: complementleft", cleft)
  ok := ok.push (s!"{name}: grades ascending, distinct", sorted)
  ok := ok.push (s!"{name}: MultiGrade(::MultiVector) round trip", roundtrip)
  ok := ok.push (s!"{name}: SparseChain ops = Chain ops", sparseOps)
  return ok.toList

/-- Run the suite (for the `lake test` driver): `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  let checks := props ℝ3 "ℝ3" 0xC11F ++ props ℝ4 "ℝ4" 0xC12F ++ props ℝ5 "ℝ5" 0xC13F
  let mut passed := 0
  let mut failed := 0
  for (lbl, ok) in checks do
    if ok then passed := passed + 1
    else
      failed := failed + 1
      IO.eprintln s!"  FAIL {lbl}"
  IO.println s!"Clifford: {passed} passed, {failed} failed"
  return (passed, failed)

end Tests.Clifford
