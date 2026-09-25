/-
Basis-blade sign rules (port-notes/grassmann-parity.md §4), bit for bit.

Sources: Grassmann.jl `src/parity.jl` (`parityjoin`, `parityinner`,
`_parityregressive`, `parityinterior`, `splitbasis`, `parityseq`), Leibniz.jl
`src/generic.jl` (`symmetricmask`, `diffcheck`, grade parities, complement
parities) and DirectSum.jl `src/operations.jl:277-324` (the per-space
complement/metric parities). Everything is a pure function of the space value
`V` and `UInt64` masks.

Metric views (§3.3): `V.sigBits` (view A: signs used by `parity`),
`V.metricAt i` (view B: hodge/metric factors) and a Gram matrix `g` (view C:
non-diagonal contractions), passed explicitly so the exact and the
Julia-compatible conformal metric share one implementation.
-/
import DirectSum.Show
import Leibniz.Combinatorics
import Leibniz.Generic

namespace DirectSum

open Bits Leibniz

/-- A list of `(blade, coefficient)` terms in insertion order (sparse multivector). -/
abbrev Terms := Array (UInt64 × Rat)

namespace Terms

/-- Add `c · e_k`, merging with an existing entry for `k`. -/
def add (t : Terms) (k : UInt64) (c : Rat) : Terms :=
  match t.findIdx? (·.1 == k) with
  | some i => t.modify i fun (k, c') => (k, c' + c)
  | none => t.push (k, c)

/-- Drop zero coefficients. -/
def nonzero (t : Terms) : Terms := t.filter (·.2 != 0)

/-- Scale every coefficient. -/
def scale (t : Terms) (c : Rat) : Terms := t.map fun (k, x) => (k, c * x)

/-- Insert a term into a list sorted by `basisRank n`, after every term of equal
or lower rank (so inserting left to right is stable). -/
def insertByRank (n : Nat) (x : UInt64 × Rat) : List (UInt64 × Rat) → List (UInt64 × Rat)
  | [] => [x]
  | y :: ys => if basisRank n x.1 < basisRank n y.1 then x :: y :: ys else y :: insertByRank n x ys

/-- Sort by position in the `n`-dimensional multivector layout. A stable
insertion sort by structural recursion: term lists here have a handful of
entries (at most `2ⁿ`, usually one to four), and unlike `Array.qsort` the
kernel can evaluate it, so `decide +kernel` checks conformal blade tables
(`Grassmann.Proofs.Conformal`). -/
def sortBasis (n : Nat) (t : Terms) : Terms :=
  (t.toList.foldl (fun acc x => insertByRank n x acc) []).toArray

end Terms

namespace TensorBundle

variable (V : TensorBundle)

/-! ## Masks and guards (`Leibniz.jl src/generic.jl:53-105`) -/

/-- Julia `symmetricmask(V,a,b) = (A, B, Q, Z)`: the exterior parts `A`, `B`
(tangent bits removed), the union `Q` of the tangent bits and the repeated
tangent bits `Z` (a nonzero `Z` makes the coefficient a lower-order blade). -/
@[inline] def symmetricmask (a b : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let d := V.diffmask
  let ad := a &&& d
  let bd := b &&& d
  (a &&& ~~~d, b &&& ~~~d, ad ||| bd, ad &&& bd)

/-- Leibniz `hasorigin(V,B)` on a mask: the `∅` bit (bit 1 if `∞` is present,
else bit 0). Does not check `V.hasorigin` (quirk Q14, callers do). -/
@[inline] def originBit (x : UInt64) : Bool := if V.hasinf then x &&& 2 == 2 else x &&& 1 == 1

/-- Julia `diffcheck(V,A,B)` (`Leibniz.jl src/generic.jl:99-105`): the product of
blades `A`, `B` vanishes because `∞` occurs in both and `∅` in neither (or the
reverse, a null vector squared), or because the total tangent order exceeds `μ`. -/
def diffcheck (a b : UInt64) : Bool :=
  let v := V.diffmask
  let conf := V.hasconformal
  let ia := a &&& 1 == 1
  let ib := b &&& 1 == 1
  let hi := conf && ia && ib && !(V.originBit a || V.originBit b)
  let ho := conf && V.originBit a && V.originBit b && !(ia || ib)
  hi || ho || (V.diffvars != 0 && popcount (a &&& v) + popcount (b &&& v) > V.diffmode)

/-- Grassmann `diffcheck2` (`src/parity.jl:79-83`): only the tangent-order test. -/
@[inline] def diffcheck2 (a b : UInt64) : Bool :=
  let v := V.diffmask
  V.diffvars != 0 && popcount (a &&& v) + popcount (b &&& v) > V.diffmode

/-- Julia `hasinf(b)` for a basis blade: the space has `∞` and `b` contains it. -/
@[inline] def bladeHasInf (b : UInt64) : Bool := V.hasinf && b &&& 1 == 1

/-- Julia `hasorigin(b)` for a basis blade. -/
@[inline] def bladeHasOrigin (b : UInt64) : Bool := V.hasorigin && V.originBit b

/-! ## Reordering and metric parity (`src/parity.jl:32-35, 354-361`) -/

/-- Julia `parityjoin(N,S,a,b)`: parity of the reordering of `e_a e_b` plus the
number of shared negative-square generators. -/
@[inline] def _root_.DirectSum.parityjoin (s a b : UInt64) : Bool :=
  reorderParity a b != Bits.parity (a &&& b &&& s)

/-- Julia `parity(V,a,b)`: `true` iff `e_a e_b = -(…) e_{a⊕b}` for the view-A
metric, tangent bits ignored (they commute). -/
@[inline] def parity (a b : UInt64) : Bool :=
  let d := ~~~V.diffmask
  parityjoin V.sigBits (a &&& d) (b &&& d)

/-- Product of the view-B metric factors `V[i]` over the generators of `b`
(1 when empty). -/
def metricProduct (b : UInt64) : Rat := go b 1 64
where
  /-- Multiply in the factor of the lowest set bit of `x`. -/
  go (x : UInt64) (acc : Rat) : Nat → Rat
    | 0 => acc
    | fuel + 1 => if x == 0 then acc else go (x &&& (x - 1)) (acc * V.metricAt (ctz x + 1)) fuel

/-- Julia `parityinner(V,a,b)` (`src/parity.jl:138-153`, diagonal/conformal
branch): `±|Π_{i∈A∩B} V[i]|`, the sign from `parity` (view A). -/
def parityinner (a b : UInt64) : Rat :=
  let (a', b', _, _) := V.symmetricmask a b
  let g := V.metricProduct (a' &&& b')
  let g := if g < 0 then -g else g
  if V.parity a' b' then -g else g

/-! ## Grade involutions (`Leibniz.jl src/generic.jl:139-153`) -/

/-- Julia `grade(V,B)`: popcount of the non-tangent bits `B & (2^grade(V)-1)`. -/
@[inline] def gradeOf (b : UInt64) : Nat := popcount (b &&& lowMask V.grade)

/-- Julia `pseudograde(V,B) = grade(V) - grade(V,B)`. -/
@[inline] def pseudogradeOf (b : UInt64) : Nat := V.grade - V.gradeOf b

/-! ## Complement parities (`DirectSum.jl src/operations.jl:277-324`) -/

/-- Julia `parityright(V,B,G)`: sign of the right complement (indices of the
non-tangent bits of `B`; `G` defaults to `popcount B`, tangent bits included). -/
@[inline] def parityright (b : UInt64) (g : Nat := popcount b) : Bool :=
  parityrightRaw (sumIndices (b &&& lowMask (V.n - V.diffvars))) g

/-- Julia `parityleft(V,B,G)`. -/
@[inline] def parityleft (b : UInt64) (g : Nat := popcount b) : Bool :=
  parityleftRaw (sumIndices (b &&& lowMask (V.n - V.diffvars))) g (V.n - V.diffvars)

/-- Julia `parityrighthodge(V,B,G)`: `±Π V[i]` over the non-tangent generators of
`B`; the conformal correction flips the sign when `B` holds `∅` without `∞`. -/
def parityrighthodge (b : UInt64) (g : Nat := popcount b) : Rat :=
  let ind := b &&& lowMask (V.n - V.diffvars)
  let m := V.metricProduct ind
  let c := V.hasconformal && (b &&& 3 == 2)
  if parityrightRaw (sumIndices ind) g != c then -m else m

/-- Julia `paritylefthodge(V,B,G)`. -/
def paritylefthodge (b : UInt64) (g : Nat := popcount b) : Rat :=
  let ind := b &&& lowMask (V.n - V.diffvars)
  let m := V.metricProduct ind
  let c := V.hasconformal && (b &&& 3 == 2)
  if parityleftRaw (sumIndices ind) g (V.n - V.diffvars) != c then -m else m

/-- Julia `paritymetric(V,B)`: `Π V[i]` over the non-tangent generators of `B`. -/
@[inline] def paritymetric (b : UInt64) : Rat := V.metricProduct (b &&& lowMask (V.n - V.diffvars))

/-- Julia `parityanti(V,B) = paritymetric(V, complement(N,B,D,P))`. -/
@[inline] def parityanti (b : UInt64) : Rat :=
  V.paritymetric (complement V.n b V.diffvars V.nulls)

/-- Julia `parityrightnull`/`parityleftnull` factor (`Leibniz.jl src/generic.jl:215-219`):
in a conformal space a blade holding exactly one of `∞`, `∅` scales its
Euclidean complement by `2` (`∞`) or `1/2` (`∅`). -/
@[inline] def nullFactor (b : UInt64) : Rat :=
  if V.hasconformal && popcount (b &&& 3) == 1 then (if b &&& 1 == 1 then 2 else 1 / 2) else 1

/-! ## Regressive product parity (`src/parity.jl:41-63`) -/

/-- Julia `_parityregressive(Signature(V),a,b,skew)` → `(neg, C, t, Z)`: the
DeMorgan regressive product `(-1)^{L(L-G)} ⋆⁻¹(⋆a ∧ ⋆b)` with the Euclidean
right complement. `t = false` means the product vanishes. Metric-independent
(the view-A term vanishes since `α`, `β` are disjoint). -/
def parityregressive (a b : UInt64) (skew : Bool := false) : Bool × UInt64 × Bool × UInt64 :=
  let n := V.n
  let d := V.diffvars
  let (a', b', q, z) := V.symmetricmask a b
  let α := complement n a' d
  let β := complement n b' d
  if α &&& β == 0 && !V.diffcheck α β then
    let c := α ^^^ β
    let l : Int := popcount a' + popcount b'
    let bas := if skew || a' != 0 || b' != 0 then complement n c d else 0
    let par := parityrightRaw (sumIndices a') (popcount a') ^^ parityrightRaw (sumIndices b') (popcount b')
      ^^ parityrightRaw (sumIndices c) (popcount c)
    let neg := ((l * (l - V.grade)) % 2 != 0) ^^ par ^^ parityjoin V.sigBits α β
    (neg, bas ||| q, true, z)
  else (false, 0, false, z)

/-! ## Compound metric rows (view C) -/

/-- Determinant of a small square `Rat` matrix (Gaussian elimination). -/
def ratDet (m : Array (Array Rat)) : Rat := Id.run do
  let n := m.size
  let mut a := m
  let mut det : Rat := 1
  for col in [0:n] do
    let piv? := (List.range n).find? fun r => r ≥ col && (a[r]!)[col]! != 0
    match piv? with
    | none => return 0
    | some p =>
      if p != col then
        let rp := a[p]!
        a := (a.set! p a[col]!).set! col rp
        det := -det
      let pv := (a[col]!)[col]!
      det := det * pv
      for r in [col + 1:n] do
        let f := (a[r]!)[col]! / pv
        if f != 0 then
          let rowc := a[col]!
          a := a.modify r fun row => row.zipIdx.map fun (x, j) => x - f * rowc[j]!
  return det

/-- The compound-metric row of blade `b`: `det g[idx b, idx K]` for every blade
`K` of the same grade among the first `grade(V)` generators (lex order),
zero entries dropped (Grassmann `metrictensor(V,G)[bladeindex(B)]`). -/
def compoundRow (g : Array (Array Rat)) (b : UInt64) : Terms :=
  let rows := indicesList b
  let gr := popcount b
  (indexBasis V.grade gr).filterMap fun k =>
    let cols := indicesList k
    let sub := rows.toArray.map fun r => cols.toArray.map fun c => ((g[r - 1]?.getD #[])[c - 1]?).getD 0
    let d := ratDet sub
    if d == 0 then none else some (k, d)

/-! ## Interior (contraction) parity (`src/parity.jl:85-131`) -/

/-- Julia `parityinterior(V,a,b,lim=true)`: the terms of `contraction(e_a, e_b)
= e_a ∨ ⋆e_b` (left contraction of `~e_b` onto `e_a`) with Gram matrix `g`
for non-diagonal spaces, plus the flag `t` (some term survived) and `Z`.
Diagonal spaces use the view-B factor `Π V[i]` of `b`; zero factors are skipped
(so a degenerate `v₃⋅v₃` is `𝟎`, not `0v`). -/
def interiorTerms (g : Array (Array Rat)) (a b : UInt64) : Terms × Bool × UInt64 :=
  let (a', b', q, z) := V.symmetricmask a b
  if V.diffcheck a' b' then (#[], false, z) else
  let gr := popcount b'
  let row : Terms := if V.isdiag then #[(b', V.metricProduct b')] else V.compoundRow g b'
  row.foldl (init := (#[], false, z)) fun (acc, tout, z) (k, gk) =>
    if gk == 0 || V.diffcheck2 a' k then (acc, tout, z) else
    let (p, c, t, _) := V.parityregressive a' (complement V.n k V.diffvars) true
    if t then
      let ggg := if p != parityrightRaw (sumIndices k) gr then -gk else gk
      (acc.add (c ||| q) ggg, true, z)
    else (acc, tout, z)

/-! ## Splitting a blade into metric-connected groups (`src/parity.jl:256-293`) -/

/-- Julia `splitbasis(V,B)`: the generators of `B` grouped into connected
components of the nonzero pattern of `g` restricted to `B` (greedy union,
groups ordered by their first member). Diagonal spaces give one group per bit. -/
def splitbasis (g : Array (Array Rat)) (b : UInt64) : List UInt64 :=
  if b == 0 then [] else
  let ind := indicesList b
  if V.isdiag then ind.map bit else
  let m := ind.length
  let entry := fun (i j : Nat) => ((g[ind[i]! - 1]?.getD #[])[ind[j]! - 1]?).getD 0
  -- f[i] = positions j (0-based) with a nonzero entry in row i, plus i itself
  let f0 : List (List Nat) := (List.range m).map fun i =>
    let row := (List.range m).filter fun j => entry i j != 0
    if row.contains i then row else row ++ [i]
  let groups := merge f0 1 (m * m + 1)
  groups.map fun grp => grp.foldl (fun acc p => acc ||| bit ind[p]!) 0
where
  /-- Julia's greedy `while j ≤ length(f)` union loop. -/
  merge (f : List (List Nat)) (j : Nat) : Nat → List (List Nat)
    | 0 => f
    | fuel + 1 =>
      if j ≥ f.length then f else
      let fj := f[j]!
      match (List.range j).find? (fun k => fj.any fun q => f[k]!.contains q) with
      | some k =>
        let fk := fj.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) f[k]!
        merge ((f.set k fk).eraseIdx j) j fuel
      | none => merge f (j + 1) fuel

/-- Julia `parityseq(V,B)`: `-1` iff an odd number of *consecutive* group pairs
reorder (only consecutive pairs are compared, Julia defect 3). -/
def parityseq (bs : List UInt64) : Int :=
  if V.isdiag || bs.length == 1 then 1 else
  let odd := (bs.zip bs.tail).foldl (fun acc (x, y) => acc != reorderParity x y) false
  if odd then -1 else 1

end TensorBundle

end DirectSum
