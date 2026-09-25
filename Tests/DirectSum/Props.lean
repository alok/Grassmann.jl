/-
Algebraic property tests of the blade layer (DESIGN.md §7), exhaustive over
every blade pair/triple of a set of small spaces:

* the diagonal rule agrees with the independent Chevalley product on the Gram
  matrix (two unrelated algorithms);
* associativity of the geometric product (diagonal, conformal, `MetricTensor`);
* `ab = a⌋b + a∧b` for vectors, graded commutativity of `∧`, `~(ab) = ~b ~a`;
* the runtime-metric skeletons reproduce `mul` and `contraction`;
* the Hodge double complement is `±1` and the complement parities satisfy
  `e_B ∧ !e_B = I` (Euclidean).
-/
import Tests.DirectSum.Common

open DirectSum DirectSum.Bits

namespace DirectSumTests.Props

/-- Multiply two term lists with the space's geometric product (exact). -/
def mulTerms (V : TensorBundle) (x y : Terms) : Terms :=
  x.foldl (init := #[]) fun acc (a, ca) =>
    y.foldl (init := acc) fun acc (b, cb) =>
      (V.mul a b).terms.foldl (fun acc (k, c) => Terms.add acc k (ca * cb * c)) acc

/-- The spaces exercised. -/
def spaces : List (String × TensorBundle) :=
  [ ("E3", ℝ^3), ("M4", S!"-+++"), ("S4", S!"+-+-"), ("I4", ℝ4), ("D3", D!"1,2,-3"),
    ("D3deg", D!"1,1,0"), ("D4", D!"2,-1,3,-4"), ("P4inf", S!"∞+++"), ("P4orig", S!"∅+++"),
    ("dual3", (S!"+-+")′), ("mixed2", ℝ^2 ⊕ (ℝ^2)′), ("C3", S!"∞∅+"), ("C4neg", S!"∞∅+-"),
    ("C5", S!"∞∅+++"), ("C3dual", (S!"∞∅+")′),
    ("MT3", .metricTensor #[#[1, 1/2, 0], #[1/2, 1, 1/2], #[0, 1/2, 1]]),
    ("MT3b", .metricTensor #[#[2, 1, 0], #[1, 0, 3], #[0, 3, -1]]) ]

/-- Run the property suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  for (nm, V) in spaces do
    let blades := Leibniz.indexBasisAll V.n
    let vecs := blades.filter (popcount · == 1)
    -- diagonal rule vs Chevalley on the Gram matrix
    if V.isdiag then
      let mut ok := true
      for a in blades do
        for b in blades do
          ok := ok && normTerms (V.mul a b).terms == normTerms (TensorBundle.cliffordProduct V.gram V.n a b)
      t := t.check ok s!"{nm}: diagonal rule ≠ Chevalley product"
    else
      -- the cached product table (n ≤ 6) agrees with the Chevalley product computed per call
      let mut ok := true
      for a in blades do
        for b in blades do
          let (a', b', q, _) := V.symmetricmask a b
          let direct := (TensorBundle.cliffordProduct V.gram V.n a' b').map fun (k, c) => (k ||| q, c)
          ok := ok && normTerms (V.mul a b).terms == normTerms direct
      t := t.check ok s!"{nm}: cached product table ≠ Chevalley product"
    -- associativity on every blade triple
    let mut assoc := true
    for a in blades do
      for b in blades do
        let ab := (V.mul a b).terms
        for c in blades do
          let lhs := mulTerms V ab #[(c, 1)]
          let rhs := mulTerms V #[(a, 1)] (V.mul b c).terms
          assoc := assoc && normTerms lhs == normTerms rhs
    t := t.check assoc s!"{nm}: geometric product not associative"
    -- vectors: ab = a⌋b + a∧b, where Grassmann's contraction(a,b) = a⋅b
    let mut split := true
    for a in vecs do
      for b in vecs do
        let sum := (V.contraction a b).terms ++ (V.wedge a b).terms
        split := split && normTerms (V.mul a b).terms == normTerms sum
    t := t.check split s!"{nm}: ab ≠ a⋅b + a∧b for vectors"
    -- graded commutativity of ∧ and reversion of products
    let mut comm := true
    let mut rev := true
    for a in blades do
      for b in blades do
        let s := if (popcount a * popcount b) % 2 == 1 then -1 else 1
        comm := comm && normTerms (V.wedge a b).terms == normTerms ((V.wedge b a).terms.scale s)
        let revAB := (V.mul a b).terms.foldl (init := #[]) fun acc (k, c) =>
          (V.reverse k).terms.foldl (fun acc (k', c') => Terms.add acc k' (c * c')) acc
        let rb := (V.reverse b).terms
        let ra := (V.reverse a).terms
        rev := rev && normTerms revAB == normTerms (mulTerms V rb ra)
    t := t.check comm s!"{nm}: ∧ not graded-commutative"
    t := t.check rev s!"{nm}: ~(ab) ≠ ~b ~a"
    -- runtime-metric skeletons (diagonal spaces)
    if V.isdiag && !V.isdyadic then
      let mut sk := true
      for a in blades do
        for b in blades do
          let viaMul : Terms := match V.mulSkeleton a b with
            | some (neg, shared, bits) =>
              let g := V.metricProduct shared
              #[(bits, if neg then -g else g)]
            | none => #[]
          let viaDot : Terms := match V.contractionSkeleton a b with
            | some (neg, m, bits) =>
              let g := V.metricProduct m
              if g == 0 then #[] else #[(bits, if neg then -g else g)]
            | none => #[]
          sk := sk && normTerms viaMul == normTerms (V.mul a b).terms
            && normTerms viaDot == normTerms (V.contraction a b).terms
      t := t.check sk s!"{nm}: runtime-metric skeleton ≠ mul/contraction"
    -- complements (not defined on dyadic spaces)
    if !V.isdyadic && V.isdiag && !V.hasconformal then
      let mut hh := true
      let mut wedgeI := true
      for b in blades do
        let g := popcount b
        let twice := match V.complementrighthodge b with
          | .ok r => V.mapLinear V.complementrighthodge r
          | .error e => .error e
        -- ⋆⋆e_B = (-1)^{g(n-g)} det(g) e_B for a diagonal metric
        let expect := (if (g * (V.n - g)) % 2 == 1 then -1 else 1) * V.metricProduct (lowMask V.n)
        hh := hh && (match twice with | .ok r => normTerms r.terms == normTerms #[(b, expect)] | _ => false)
        -- e_B ∧ !e_B = I (Euclidean right complement)
        match V.complementright b with
        | .ok (.single c d) => wedgeI := wedgeI && normTerms ((V.wedge b d).terms.scale c) == #[(lowMask V.n, 1)]
        | _ => wedgeI := false
      t := t.check hh s!"{nm}: ⋆⋆ ≠ ±det"
      t := t.check wedgeI s!"{nm}: e_B ∧ !e_B ≠ I"
  return t

end DirectSumTests.Props
