/-
Bug-compatible port of Grassmann's non-diagonal geometric product
`paritygeometric` (`src/parity.jl:166-314`, port-notes/grassmann-parity.md
§4.5.2), used only to account for Julia's documented defects in the oracle
tests:

* defect 1: conformal spaces use Julia's hard-coded Gram matrix (`gramJulia`),
  so `S"∞∅+-"` treats its `-` generator as `+`;
* defect 2: a `MetricTensor` with two multi-vector metric groups loses its
  middle-grade terms (the "contraction + wedge" split is exact only when the
  split factor is a vector);
* defect 3: `parityseq` compares only consecutive groups.

`DirectSum.TensorBundle.mul` is the exact product; these functions reproduce
what Julia prints so the test suite can prove a mismatch is one of these
defects rather than a porting error.
-/
import DirectSum.BladeAlgebra

namespace DirectSum.Compat

open Bits Leibniz

/-- `((E, Eg), (I, Ig))`: the coefficient `Eg·Ig` of `e_{E ∪ I}` with `I` the part
still available for contraction. -/
abbrev State := (UInt64 × Rat) × (UInt64 × Rat)

variable (V : TensorBundle)

/-- Julia `interior(V,a,b)` (`lim = false`) under Julia's Gram matrix:
`(g, C, t)` with `g` summed over all terms. -/
def interior (a b : UInt64) : Rat × UInt64 × Bool :=
  let (ts, t, _) := V.interiorTerms V.gramJulia a b
  (ts.foldl (fun acc (_, x) => acc + x) 0, ts[0]?.map (·.1) |>.getD 0, t)

/-- The contraction part of one right-expansion step (`paritygeometricright`). -/
private def stepRight (s : State) (b : UInt64) : List State :=
  let ((ae, aeg), (ai, aig)) := s
  let g := popcount b
  let flip := parityclifford g != (g * popcount ai % 2 == 1)
  let ccg : List State :=
    if V.isdiag || V.hasconformal then
      let (gg, c, t) := interior V ai b
      let cg := if flip then -(aig * gg) else aig * gg
      if t then [((ae, aeg), (c, cg))] else []
    else
      let (ts, _, _) := V.interiorTerms V.gramJulia ai b
      let gg := if flip then -(aig * aeg) else aig * aeg
      ts.toList.map fun cg => ((ae, gg), cg)
  if ai &&& b == 0 then
    let p := if reorderParity (ai ^^^ ae) b then -aeg else aeg
    ((ae ^^^ b, p * aig), (ai, 1)) :: ccg
  else ccg

/-- One left-expansion step (`paritygeometricleft`). -/
private def stepLeft (a : UInt64) (s : State) : List State :=
  let ((be, beg), (bi, big)) := s
  let g := popcount a
  let ccg : List State :=
    if V.isdiag || V.hasconformal then
      let (gg, c, t) := interior V bi a
      let cg := if parityreverse g then -(big * gg) else big * gg
      if t then [((be, beg), (c, cg))] else []
    else
      let (ts, _, _) := V.interiorTerms V.gramJulia bi a
      let gg := if parityreverse g then -(big * beg) else big * beg
      ts.toList.map fun cg => ((be, gg), cg)
  if a &&& bi == 0 then
    let p := if reorderParity a (be ^^^ bi) then -beg else beg
    ((a ^^^ be, p * big), (bi, 1)) :: ccg
  else ccg

/-- Julia `combinebasis`: `E ∪ I` for every state with `E ∩ I = ∅` (not merged). -/
private def combine (vals : List State) : Terms :=
  (vals.filterMap fun ((e, eg), (i, ig)) => if e &&& i == 0 then some (e ^^^ i, eg * ig) else none).toArray

/-- Julia `paritygeometric(V,A,B)`: the (unmerged) term list of `e_A e_B`. -/
def paritygeometric (a b : UInt64) : Terms :=
  let g := V.gramJulia
  let as := V.splitbasis g a
  let bs := V.splitbasis g b
  let maxpc := fun (l : List UInt64) => l.foldl (fun m x => max m (popcount x)) 0
  let ga := maxpc as
  let gb := maxpc bs
  if (if ga ≤ 1 && gb ≤ 1 then popcount a ≥ popcount b else ga ≥ gb) then
    match bs with
    | [] => combine [((0, 1), (a, 1))]
    | b0 :: rest =>
      let init := stepRight V ((0, (V.parityseq bs : Rat)), (a, 1)) b0
      combine (rest.foldl (fun vals grp => vals.flatMap fun s => stepRight V s grp) init)
  else
    match as.reverse with
    | [] => combine [((0, 1), (b, 1))]
    | alast :: rest =>
      let init := stepLeft V alast ((0, (V.parityseq as : Rat)), (b, 1))
      combine (rest.foldl (fun vals grp => vals.flatMap fun s => stepLeft V grp s) init)

/-- Julia `a * b` as the oracle computes it: identical to `TensorBundle.mul` for
diagonal spaces, `paritygeometric` summed for non-diagonal ones. -/
def mul (a b : UInt64) : BladeResult :=
  if V.isdiag then V.mul a b
  else
    let t := paritygeometric V a b
    .ofTerms V.n (t.foldl (fun acc (k, c) => acc.add k c) #[])

/-- Julia `contraction(a,b)` under Julia's Gram matrix (defect 1 for conformal
spaces with negative Euclidean generators). -/
def contraction (a b : UInt64) : BladeResult :=
  let (ts, t, z) := V.interiorTerms V.gramJulia a b
  if V.isdiag || V.hasconformal then
    if !t then .zero else
    let c := ts[0]?.map (·.1) |>.getD 0
    let g := ts.foldl (fun acc (_, x) => acc + x) 0
    V.nestTangent z (if g == 1 then .blade c else .single g c)
  else .ofTerms V.n ts

/-- Julia `complementrighthodge` with Julia's product for `MetricTensor` spaces. -/
def complementrighthodge (b : UInt64) : Except String BladeResult :=
  if !V.isdiag && !V.hasconformal then
    V.mapLinear (fun r => .ok (mul V r V.pseudoscalar)) (V.reverse b)
  else V.complementrighthodge b

/-- Julia `metric(b)` with Julia's product for `MetricTensor` spaces. -/
def bladeMetric (b : UInt64) : Except String BladeResult := do
  if !V.isdiag && !V.hasconformal then
    V.mapLinear V.complementleft (← complementrighthodge V b)
  else V.bladeMetric b

/-- Julia `complementlefthodge(b)` with Julia's product for `MetricTensor` spaces. -/
def complementlefthodge (b : UInt64) : Except String BladeResult := do
  if !V.isdiag && !V.hasconformal then V.mapLinear V.complementleft (← bladeMetric V b)
  else V.complementlefthodge b

/-- Julia `cross(a,b)` with Julia's product for `MetricTensor` spaces. -/
def cross (a b : UInt64) : Except String BladeResult :=
  V.mapLinear (complementrighthodge V) (V.wedge a b)

/-- Julia's container metric (lowering with Julia's Gram matrix). -/
def metricChain (b : UInt64) : Terms :=
  if V.isdiag then #[(b, V.paritymetric b)] else V.compoundRow V.gramJulia b

/-- Julia's container `complementrighthodge` (Julia's Gram matrix). -/
def complementrighthodgeChain (b : UInt64) : Except String Terms := do
  if V.isdyadic then throw "Complement for dyadic tensors is undefined"
  if V.isdiag then return #[(complement V.n b V.diffvars 0, V.parityrighthodge b)]
  let parts ← (metricChain V b).mapM fun (k, g) => return (← V.complementrightChain k).scale g
  return parts.foldl (fun acc p => p.foldl (fun acc (k, x) => acc.add k x) acc) #[]

/-- Julia's container `complementlefthodge` (Julia's Gram matrix). -/
def complementlefthodgeChain (b : UInt64) : Except String Terms := do
  if V.isdyadic then throw "Complement for dyadic tensors is undefined"
  if V.isdiag then return #[(complement V.n b V.diffvars 0, V.paritylefthodge b)]
  let parts ← (metricChain V b).mapM fun (k, g) => return (← V.complementleftChain k).scale g
  return parts.foldl (fun acc p => p.foldl (fun acc (k, x) => acc.add k x) acc) #[]

end DirectSum.Compat
