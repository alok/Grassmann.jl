/-
Blade-level products, involutions and complements (port-notes/grassmann-parity.md
§4.2–4.11), returning Julia's result *kinds*: `𝟎`, a bare basis blade, a
`Single` (coefficient × blade), or a sum of several terms.

* Diagonal spaces (`Int`, non-conformal `Signature`, `DiagonalForm`, including
  degenerate zeros) follow Grassmann `mul` (`src/algebra.jl:43-55`) exactly.
* Non-diagonal spaces (conformal `∞∅`, `MetricTensor`) use the Chevalley
  recursion `e_{a₁}∧e_{A'} = e_{a₁}e_{A'} - e_{a₁}⌋e_{A'}` over the true Gram
  matrix (the `truth.py` ground truth). It agrees with Julia on `S"∞∅+"` and
  `S"∞∅+++"` and fixes Julia defects 1 (`S"∞∅+-"` ignores the `-`) and 2
  (`MetricTensor` drops middle grades). The bug-compatible Julia algorithm lives
  in `DirectSum.Compat`.
* Tangent (`∂`) bits commute and never contribute a sign; a repeated `∂` makes
  the coefficient a blade of `loworder(V)` (`BladeResult.nested`).

Hot paths for code generation: `mulSign` (signature spaces, allocation-free)
and `mulDiag` (diagonal spaces).
-/
import DirectSum.Parity

namespace DirectSum

open Bits Leibniz

/-- The result of a blade-level operation, mirroring Julia's result types. -/
inductive BladeResult where
  /-- Julia `Zero` (`𝟎`). -/
  | zero
  /-- A bare basis blade (Julia `Submanifold`, coefficient `+1`). -/
  | blade (bits : UInt64)
  /-- Julia `Single`: coefficient times blade (printed with the coefficient, `1v`). -/
  | single (coef : Rat) (bits : UInt64)
  /-- A sum of terms (Julia prints a `Chain`/`Spinor`/`Multivector`), in basis order. -/
  | sum (terms : Terms)
  /-- Tangent case: `e_z` of `loworder(V)` (a repeated `∂`) times `inner`
  (Julia `Single{V}(getbasis(loworder(V),Z), inner)`, printed `∂₁⊗…`). -/
  | nested (z : UInt64) (inner : BladeResult)
  deriving Repr, BEq, Inhabited

namespace BladeResult

/-- The terms `(blade, coefficient)` (a nested result reports its inner terms). -/
def terms : BladeResult → Terms
  | zero => #[]
  | blade b => #[(b, 1)]
  | single c b => #[(b, c)]
  | sum t => t
  | nested _ r => r.terms

/-- Multiply by a scalar (a bare blade becomes a `Single`, as Julia `c*b` does). -/
def scale (c : Rat) : BladeResult → BladeResult
  | zero => zero
  | blade b => single c b
  | single c' b => single (c * c') b
  | sum t => sum (t.scale c)
  | nested z r => nested z (r.scale c)

/-- Julia `+(Single{V}.(terms)...)` for the result of a non-diagonal product:
empty → `𝟎`, one term → `Single`, otherwise a sum (zero coefficients dropped,
basis order). -/
def ofTerms (n : Nat) (t : Terms) : BladeResult :=
  match (t.nonzero.sortBasis n) with
  | #[] => zero
  | #[(b, c)] => single c b
  | t => sum t

/-- Wrap `inner` with the repeated-tangent coefficient `e_z` when `z ≠ 0`. -/
@[inline] def withTangent (diffvars : Nat) (z : UInt64) (inner : BladeResult) : BladeResult :=
  if diffvars != 0 && z != 0 then nested z inner else inner

end BladeResult

namespace TensorBundle

variable (V : TensorBundle)

/-! ## Grade involutions (`DirectSum.jl src/generic.jl:220-234`) -/

/-- `b` if the parity is even, else `-1·b`. -/
@[inline] private def signed (p : Bool) (b : UInt64) : BladeResult :=
  if p then .single (-1) b else .blade b

/-- Julia `reverse(b)` (`~b`, also `conj`): negate grades `≡ 2,3 (mod 4)`
(grade counts non-tangent bits only). -/
def reverse (b : UInt64) : BladeResult := signed (parityreverse (V.gradeOf b)) b

/-- Julia `involute(b)`: negate odd grades. -/
def involute (b : UInt64) : BladeResult := signed (parityinvolute (V.gradeOf b)) b

/-- Julia `clifford(b)` = `involute ∘ reverse`. -/
def clifford (b : UInt64) : BladeResult := signed (parityclifford (V.gradeOf b)) b

/-- Julia `conj(b)`, identical to `reverse`. -/
def conj (b : UInt64) : BladeResult := signed (parityconj (V.gradeOf b)) b

/-- Julia `pseudoreverse(b)` = `antireverse`: reverse by pseudograde. -/
def antireverse (b : UInt64) : BladeResult := signed (parityreverse (V.pseudogradeOf b)) b

/-- Julia `pseudoinvolute(b)` = `antiinvolute`. -/
def antiinvolute (b : UInt64) : BladeResult := signed (parityinvolute (V.pseudogradeOf b)) b

/-- Julia `pseudoclifford(b)` = `anticlifford`. -/
def anticlifford (b : UInt64) : BladeResult := signed (parityclifford (V.pseudogradeOf b)) b

/-- Sign of `reverse` on component `b` of a grade-`g` `Chain` (Grassmann Chain
kernel, `src/products.jl:1816-1976`): per grade when `diffvars = 0`, per blade
otherwise. -/
def reverseChainSign (g : Nat) (b : UInt64) : Bool :=
  if V.diffvars == 0 then parityreverse g else parityreverse (V.gradeOf b)

/-- Sign of `antireverse` on component `b` of a grade-`g` `Chain`:
`parityreverse(n - g)` when `diffvars = 0`, else by the blade's pseudograde. -/
def antireverseChainSign (g : Nat) (b : UInt64) : Bool :=
  if V.diffvars == 0 then parityreverse (V.n - g) else parityreverse (V.pseudogradeOf b)

/-! ## Exterior product (`src/algebra.jl:127-147`) -/

/-- Julia `a ∧ b`: `𝟎` if the blades share a generator (or `diffcheck`), else
`±e_{a∪b}`; the sign is the reordering parity (the metric is irrelevant). -/
def wedge (a b : UInt64) : BladeResult :=
  let (a', b', q, z) := V.symmetricmask a b
  if a' &&& b' != 0 || V.diffcheck a b then .zero
  else .withTangent V.diffvars z (signed (V.parity a b) ((a' ^^^ b') ||| q))

/-! ## Geometric product -/

/-- Allocation-free geometric product sign for signature spaces without tangent
or conformal structure: `e_a e_b = (-1)^{mulSign} e_{a xor b}`. -/
@[inline] def mulSign (a b : UInt64) : Bool := parityjoin V.sigBits a b

/-- Diagonal geometric product `e_a e_b = c · e_{(A⊕B)|Q}` (Julia `mul`, diagonal
branch): coefficient `±1` for disjoint blades, `±Π|gᵢᵢ|` over shared generators
otherwise (sign from view A, so `D"1,2,-3"`: `v₃v₃ = -3`, degenerate `0`). -/
def mulDiag (a b : UInt64) : Rat × UInt64 :=
  let (a', b', q, _) := V.symmetricmask a b
  let d := (a' ^^^ b') ||| q
  if a' &&& b' == 0 then (if V.parity a b then -1 else 1, d) else (V.parityinner a' b', d)

/-! ### Chevalley product (any symmetric bilinear form) -/

/-- `e_i ⌋ X` for generator `i` (0-based) under Gram matrix `g`. -/
private def lcontrVec (g : Array (Array Rat)) (i : Nat) (x : Terms) : Terms :=
  x.foldl (init := #[]) fun acc (k, c) =>
    (indicesList k).zipIdx.foldl (init := acc) fun acc (p, j) =>
      let gij := ((g[i]?.getD #[])[p - 1]?).getD 0
      if gij == 0 then acc
      else acc.add (k &&& ~~~(bit p)) (if j % 2 == 0 then c * gij else -(c * gij))

/-- `e_i ∧ X` for generator `i` (0-based). -/
private def wedgeVec (i : Nat) (x : Terms) : Terms :=
  x.foldl (init := #[]) fun acc (k, c) =>
    if testBit k i then acc
    else acc.add (k ||| shl 1 i) (if popcount (k &&& lowMask i) % 2 == 0 then c else -c)

/-- `e_A X` in the outer-product basis by the Chevalley recursion
`e_A = e_{a₁} e_{A'} - e_{a₁} ⌋ e_{A'}` (`a₁` the lowest generator of `A`). -/
private def bladeMul (g : Array (Array Rat)) : Nat → UInt64 → Terms → Terms
  | 0, _, x => x
  | fuel + 1, a, x =>
    if a == 0 then x else
    let i := ctz a
    let a' := a &&& (a - 1)
    let rest := bladeMul g fuel a' x
    let out := (wedgeVec i rest).foldl (fun acc (k, c) => acc.add k c) (lcontrVec g i rest)
    (lcontrVec g i #[(a', 1)]).foldl (init := out) fun out (k, c) =>
      (bladeMul g fuel k x).foldl (fun out (k', v) => out.add k' (-(c * v))) out

/-- The Clifford product `e_a e_b` for an arbitrary symmetric Gram matrix `g`
(outer-product basis), as nonzero terms in basis order. This is the exact
product for every metric (port-notes/grassmann-parity.md §8.2, `truth.py`). -/
def cliffordProduct (g : Array (Array Rat)) (n : Nat) (a b : UInt64) : Terms :=
  (bladeMul g (popcount a + 1) a #[(b, 1)]).nonzero.sortBasis n

/-- Julia `a * b` (geometric product, `src/algebra.jl:43-59`). Diagonal spaces:
bare blade for disjoint `+` products, `Single(-1)` for `-`, `Single(±g)` whenever
generators are shared (`v₁*v₁` is `1v`, degenerate `v₃*v₃` is `0v`).
Non-diagonal spaces: the exact Chevalley product over `V.gram`. -/
def mul (a b : UInt64) : BladeResult :=
  if V.isdiag then
    if V.istangent && V.diffcheck a b then .zero else
    let (a', b', _, z) := V.symmetricmask a b
    let (c, d) := V.mulDiag a b
    let inner := if a' &&& b' == 0 then signed (c < 0) d else .single c d
    .withTangent V.diffvars z inner
  else
    let (a', b', q, _) := V.symmetricmask a b
    .ofTerms V.n ((cliffordProduct V.gram V.n a' b').map fun (k, c) => (k ||| q, c))

/-! ## Regressive product (`src/algebra.jl:156-175`) -/

/-- Julia `a ∨ b`: `(-1)^{L(L-n)} ⋆⁻¹(⋆a ∧ ⋆b)` with the Euclidean complement
(metric-independent); bare blade when the sign is `+`. -/
def vee (a b : UInt64) : BladeResult :=
  let (neg, c, t, z) := V.parityregressive a b
  if !t then .zero else .withTangent V.diffvars z (signed neg c)

/-! ## Interior product (`src/algebra.jl:209-223`) -/

/-- Julia `contraction(a,b)` (`a ⋅ b`, `a ⨽ b`) `= a ∨ ⋆b = ⟨~b a⟩`: the left
contraction of `~e_b` onto `e_a` (`v₁₂⋅v₂ = -v₁`, `v₁₂⋅v₁₂ = +v`). Diagonal
and conformal spaces give one term (bare blade when the factor is `1`); a
`MetricTensor` can give several. Non-diagonal spaces use the true Gram matrix. -/
def contraction (a b : UInt64) : BladeResult :=
  let (ts, t, z) := V.interiorTerms V.gram a b
  if V.isdiag || V.hasconformal then
    if !t then .zero else
    let c := ts[0]?.map (·.1) |>.getD 0
    let g := ts.foldl (fun acc (_, x) => acc + x) 0
    .withTangent V.diffvars z (if g == 1 then .blade c else .single g c)
  else .ofTerms V.n ts

/-- Julia `a < b` / `a ⨼ b` = `contraction(b, a)`. -/
@[inline] def contractionLeft (a b : UInt64) : BladeResult := V.contraction b a

/-! ## Complements (`DirectSum.jl src/operations.jl:326-356`) -/

/-- Julia's error for complements in `V⊕V'`. -/
def mixedComplementError : String := "Complement for mixed tensors is undefined"

/-- Julia `complementright(b)` (`!b`): Euclidean right complement. Always a
`Single`; conformal blades holding one null generator scale by `2`/`1/2`. -/
def complementright (b : UInt64) : Except String BladeResult :=
  if V.isdyadic then .error mixedComplementError else
  .ok (.single ((if V.parityright b then -1 else 1) * V.nullFactor b)
    (complement V.n b V.diffvars 0))

/-- Julia `complementleft(b)`. -/
def complementleft (b : UInt64) : Except String BladeResult :=
  if V.isdyadic then .error mixedComplementError else
  .ok (.single ((if V.parityleft b then -1 else 1) * V.nullFactor b)
    (complement V.n b V.diffvars 0))

/-- The pseudoscalar of the non-tangent generators (Julia `V(I)`). -/
@[inline] def pseudoscalar : UInt64 := lowMask (V.n - V.diffvars)

/-- Linear extension of a blade map to a `BladeResult`. -/
def mapLinear (f : UInt64 → Except String BladeResult) (r : BladeResult) :
    Except String BladeResult := do
  match r with
  | .zero => return .zero
  | .blade b => f b
  | .single c b => return (← f b).scale c
  | .sum t =>
    let parts ← t.mapM fun (b, c) => return ((← f b).scale c).terms
    return .ofTerms V.n (parts.foldl (fun acc p => p.foldl (fun acc (k, x) => acc.add k x) acc) #[])
  | .nested z r => return .nested z (← mapLinear f r)

/-- Julia `complementrighthodge(b)` (`⋆b`, `hodge`): coefficient `±Π gᵢᵢ` at the
complement with the conformal null pair handled (`P = hasinf + hasorigin`).
A `MetricTensor` uses `~b * I` (geometric product with the pseudoscalar). -/
def complementrighthodge (b : UInt64) : Except String BladeResult :=
  if !V.isdiag && !V.hasconformal then
    V.mapLinear (fun r => .ok (V.mul r V.pseudoscalar)) (V.reverse b)
  else if V.isdyadic then .error mixedComplementError
  else .ok (.single (V.parityrighthodge b) (complement V.n b V.diffvars V.nulls))

/-- Julia `metric(b)` (`DirectSum.jl src/operations.jl:358-381`): `Π gᵢᵢ · b`;
`𝟎` for a lone `∞` or `∅` in a non-conformal space; conformal and
`MetricTensor` spaces go through `complementleft(complementrighthodge(b))`. -/
def bladeMetric (b : UInt64) : Except String BladeResult := do
  if !V.isdiag || V.hasconformal then
    V.mapLinear V.complementleft (← V.complementrighthodge b)
  else if V.isdyadic then throw mixedComplementError
  else if V.bladeHasOrigin b != V.bladeHasInf b then return .zero
  else return .single (V.paritymetric b) b

/-- Julia `complementlefthodge(b)`: like `complementrighthodge` with the left
parity; a `MetricTensor` uses `complementleft(metric(b))`. -/
def complementlefthodge (b : UInt64) : Except String BladeResult := do
  if !V.isdiag && !V.hasconformal then V.mapLinear V.complementleft (← V.bladeMetric b)
  else if V.isdyadic then throw mixedComplementError
  else return .single (V.paritylefthodge b) (complement V.n b V.diffvars V.nulls)

/-- Julia `antimetric(b)`: `Π_{i ∉ b} gᵢᵢ · b` (`parityanti`); `𝟎` for a lone
null generator. Julia throws `UndefVarError: antimetric_term` for conformal and
`MetricTensor` spaces (defect 5); here those use
`complementrighthodge(complementleft(b))`, which equals `parityanti` on every
diagonal space (checked against the oracle). -/
def antimetric (b : UInt64) : Except String BladeResult := do
  if !V.isdiag || V.hasconformal then
    V.mapLinear V.complementrighthodge (← V.complementleft b)
  else if V.isdyadic then throw mixedComplementError
  else if V.bladeHasOrigin b != V.bladeHasInf b then return .zero
  else return .single (V.parityanti b) b

/-- Julia `complementrightanti(b) = complementright(antimetric(b))`. -/
def complementrightanti (b : UInt64) : Except String BladeResult := do
  V.mapLinear V.complementright (← V.antimetric b)

/-- Julia `complementleftanti(b) = complementleft(antimetric(b))`. -/
def complementleftanti (b : UInt64) : Except String BladeResult := do
  V.mapLinear V.complementleft (← V.antimetric b)

/-- Julia `cross(a,b) = ⋆(a ∧ b)` (`AbstractTensors.jl:349`). -/
def cross (a b : UInt64) : Except String BladeResult :=
  V.mapLinear V.complementrighthodge (V.wedge a b)

/-! ### Coefficient-container complements (grassmann-parity.md §4.9.3)

Grassmann's `Chain`/`Multivector` complement kernels (`src/products.jl:1324-1487`)
differ from the blade rules: no null scaling, and the Hodge complement of a
non-diagonal space goes through the metric. These give the image of one
component `e_b` of such a container (multiply by the coefficient). Julia throws
`UndefVarError: args` for tangent spaces (defect 6); the formulas here extend
to them unchanged. -/

/-- Container `complementright`: `±e_{complement(b)}`, no null scaling. -/
def complementrightChain (b : UInt64) : Except String Terms :=
  if V.isdyadic then .error "Complement for dyadic tensors is undefined" else
  .ok #[(complement V.n b V.diffvars 0, if V.parityright b then -1 else 1)]

/-- Container `complementleft`. -/
def complementleftChain (b : UInt64) : Except String Terms :=
  if V.isdyadic then .error "Complement for dyadic tensors is undefined" else
  .ok #[(complement V.n b V.diffvars 0, if V.parityleft b then -1 else 1)]

/-- Container metric (lowering with the Gram matrix): `e_b ↦ Σ_K det g[b,K] e_K`. -/
def metricChain (b : UInt64) : Terms :=
  if V.isdiag then #[(b, V.paritymetric b)] else V.compoundRow V.gram b

/-- Container `complementrighthodge`: diagonal spaces place
`parityrighthodge(b)` at `complement(n,b,D)` (`P = 0`); non-diagonal spaces
(conformal included) use `complementright(metric(x))`. -/
def complementrighthodgeChain (b : UInt64) : Except String Terms := do
  if V.isdyadic then throw "Complement for dyadic tensors is undefined"
  if V.isdiag then return #[(complement V.n b V.diffvars 0, V.parityrighthodge b)]
  let parts ← (V.metricChain b).mapM fun (k, g) => return (← V.complementrightChain k).scale g
  return parts.foldl (fun acc p => p.foldl (fun acc (k, x) => acc.add k x) acc) #[]

/-- Container `complementlefthodge`. -/
def complementlefthodgeChain (b : UInt64) : Except String Terms := do
  if V.isdyadic then throw "Complement for dyadic tensors is undefined"
  if V.isdiag then return #[(complement V.n b V.diffvars 0, V.paritylefthodge b)]
  let parts ← (V.metricChain b).mapM fun (k, g) => return (← V.complementleftChain k).scale g
  return parts.foldl (fun acc p => p.foldl (fun acc (k, x) => acc.add k x) acc) #[]

end TensorBundle

end DirectSum
