/-
Unary maps on dynamic elements with Julia's result kinds (Grassmann.jl
`src/products.jl:1324-1976`, `src/parity.jl:463-526`, `src/multivectors.jl:1107-1144`;
DirectSum.jl `src/generic.jl:220-233`, `src/operations.jl:336-402`;
port-notes/grassmann-products.md §4.9, grassmann-types.md §4.4).

Values come from the static layer (`Grassmann.Algebra.Unary`, the container-level
plans of `Grassmann.Kernel.Reference`); the kinds follow Julia's methods:

| map | term (`One`/blade/`Single`) | `Chain{G}` | `Spinor`/`CoSpinor` | `Multivector` | `Couple`/`PseudoCouple` |
|---|---|---|---|---|---|
| `reverse` `involute` `clifford` `antireverse` | a blade stays a blade when its sign is `+`, else `Single(-1)`; a `Single` with value `0` is `Zero` | same | same | same | same, both parts signed |
| complements (`!`, `complementleft`, `⋆`, `complementlefthodge`) | `Single` on the complement blade | `Chain{n-G}` | parity flips when `n` is odd | same | `Single{I}(re) + c(imaginary)`, `c(volume) + c(imaginary)` |
| `metric` `antimetric` | `Single` | same | same | same | `metric(scalar) + metric(imaginary)`, … |
| `even` `odd` `real` `imag` | itself or `Zero` by grade | itself or `Zero` | Julia's per-size rules (`real(Quaternion) = scalar`, …) | `Spinor`/`CoSpinor`, per-size rules | by parts |
| `scalar` … `volume`, `grade(·, k)` | itself or `Zero` | itself, `Zero`; `scalar(Chain{0})` is a `Single` | the grade block or `Zero` | a `Chain` | by parts |

Fixed Julia defects (oracle `defects.json`): `antireverse-couple` (both parts are
signed), `antimetric-couple-scalar` (the scalar part is scaled), `trivector-couple`,
`volume-scalar-chain` (`volume(Chain{0}) = 𝟎`), `conformal-blade-complement` and
`projective-blade-metric` (terms use the container-level values), `zero-method-gaps`
(`metric(𝟎) = antireverse(𝟎) = 𝟎`), `multivector-of-zero`.
-/
import Grassmann.Dynamic.Arith
import Grassmann.Algebra.Unary

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-! ## Helpers -/

/-- The coefficient of blade `c` in the container-level image of blade `b` under `op`
(`Grassmann.Kernel.unTermsC`, the semantics of Julia's `Chain`/`Multivector` maps). -/
def unCoeff (V : TensorBundle) (op : UnOp) (b c : UInt64) : Rat :=
  match Kernel.unTermsC V op b with
  | .ok ts => (ts.find? fun t => t.bits == c && t.z == 0).map (·.coef) |>.getD 0
  | .error _ => 0

/-- The blade complement `I ⊻ b` (Julia `complement(n, b)` without tangent generators). -/
@[inline] def complementBits (V : TensorBundle) (b : UInt64) : UInt64 := pseudoBits V ^^^ b

/-- The term of a blade under a sign map (Julia `reverse(b::Submanifold)`): the blade
itself for sign `+`, else `Single(-1, b)`. -/
def signedBlade (V : TensorBundle) (op : UnOp) (b : UInt64) : TA V α :=
  if bladeFactor V op b == 1 then ofBlade b else single b (scaleBy (bladeFactor V op b) Coeff.one)

/-- Julia `parityreverse(G)`: whether the reverse flips grade `G` (`G mod 4 ∈ {2, 3}`). -/
@[inline] def reverseFlips (G : Nat) : Bool := G % 4 == 2 || G % 4 == 3

/-- The grade-`G` block of a multivector as a dynamic chain. -/
@[inline] def multiGrade (m : Multivector V α) (G : Nat) : TA V α := chain G (m.grade G)

/-- The grade-`G` block of a half as a dynamic chain. -/
@[inline] def halfGrade {p : Bool} (h : Half V p α) (G : Nat) : TA V α := chain G (h.grade G)

/-- Julia `Single{V,n,I}(x)`: `x` times the pseudoscalar. -/
@[inline] def topSingle (x : α) : TA V α := single (pseudoBits V) x

/-- The last coefficient of a container (Julia `t.v[end]`). -/
@[inline] def lastCoeff {n : Nat} (v : Values α n) : α := getD v (n - 1)

/-! ## Entry-wise container maps -/

/-- Whether `op` sends every blade to one multiple of one blade (involutions, the
metric-free complements, and the metric maps and Hodge complements of diagonal metrics,
outside tangent spaces). Julia then maps containers
entry by entry, copying or negating entries (`-0.0` survives); other maps (the
conformal metric) go through the static kernels. -/
def monomial (V : TensorBundle) (op : UnOp) : Bool :=
  !V.istangent && (match op with
    | .metric | .antimetric | .complementrighthodge | .complementlefthodge => V.isdiag
    | _ => true)

/-- Whether `op` is a complement (the image of blade `b` is on `I ⊻ b`). -/
def isComplement : UnOp → Bool
  | .complementright | .complementleft | .complementrighthodge | .complementlefthodge => true
  | _ => false

/-- The source blade of output blade `β` under a monomial map. -/
@[inline] def sourceBlade (V : TensorBundle) (op : UnOp) (β : UInt64) : UInt64 :=
  if isComplement op then complementBits V β else β

/-- A monomial map on the coefficient function `f` of an element: the coefficient of
output blade `β` (Julia `out[complement(B)] = p(V,B)·val`). -/
@[inline] def monoCoeff (op : UnOp) (f : UInt64 → α) (β : UInt64) : α :=
  let src := sourceBlade V op β
  scaleBy (unCoeff V op src β) (f src)

/-- A chain under a unary map, into grade `H` (`G` or `n - G`). -/
def chainMap (op : UnOp) {G : Nat} (H : Nat) (c : Chain V G α) : Chain V H α :=
  if monomial V op then chainOf V H (monoCoeff (V := V) op c.coeff)
  else ⟨Kernels.un op (.chain G) (.chain H) c.v⟩

/-- A half under a unary map, into parity `q`. -/
def halfMap (op : UnOp) {p : Bool} (q : Bool) (h : Half V p α) : Half V q α :=
  if monomial V op then halfOf V q (monoCoeff (V := V) op h.coeff)
  else ⟨Kernels.un op (halfLayout p) (halfLayout q) h.v⟩

/-- A multivector under a unary map. -/
def multiMap (op : UnOp) (m : Multivector V α) : Multivector V α :=
  if monomial V op then
    Multivector.ofFn fun i =>
      let β := fullBlade V.n i.1
      let src := sourceBlade V op β
      scaleBy (unCoeff V op src β) (getD m.v (Leibniz.basisRank V.n src))
  else Multivector.unop op m

/-- Keep the grades `keep g` of a multivector (entries copied, the others zero). -/
def multiKeep (keep : Nat → Bool) (m : Multivector V α) : Multivector V α :=
  Multivector.ofFn fun i => if keep (popcount (fullBlade V.n i.1)) then m.v.get i else Coeff.zero

/-- Keep the grades `keep g` of a half. -/
def halfKeep {p : Bool} (keep : Nat → Bool) (h : Half V p α) : Half V p α :=
  Half.ofFn fun j => if keep (popcount (((halfLayout p).blades V.n)[j.1]!)) then h.v.get j else Coeff.zero

/-! ## Involutions -/

/-- A sign map (`reverse`, `involute`, `clifford`, `antireverse`, …) with Julia's kinds
(DirectSum `src/generic.jl:220-233`, Grassmann `src/products.jl:1816-1976`). -/
def signMap (op : UnOp) : TA V α → TA V α
  | zero => zero
  | infinity => infinity
  | one => signedBlade V op 0
  | blade b => signedBlade V op b
  | single b x => if Coeff.isZero x then zero else single b (scaleBy (bladeFactor V op b) x)
  | chain g c => chain g (chainMap op g c)
  | spinor h => spinor (halfMap op false h)
  | cospinor h => cospinor (halfMap op true h)
  | multi m => multi (multiMap op m)
  | couple b re im => ofCouple (Couple.unop op ⟨b, re, im⟩)
  | pseudo b re im => ofPseudoCouple (PseudoCouple.unop op ⟨b, re, im⟩)
  | phasor amp θ => phasor amp (signMap op θ)

/-- Julia `reverse(x)` (`~x`). -/
@[inline] def reverse (x : TA V α) : TA V α := signMap .reverse x
/-- Julia `involute(x)`. -/
@[inline] def involute (x : TA V α) : TA V α := signMap .involute x
/-- Julia `clifford(x)`. -/
@[inline] def clifford (x : TA V α) : TA V α := signMap .clifford x
/-- Julia `antireverse(x)` (`pseudoreverse`). -/
@[inline] def antireverse (x : TA V α) : TA V α := signMap .antireverse x

/-! ## Complements and metrics -/

/-- A term's image under a complement-type map: a `Single` (DirectSum
`src/operations.jl:346-352`) with the container-level value; a zero image stays a
`Single` on the complement blade, and a conformal Hodge image of several blades is
their sum. -/
def compTerm (op : UnOp) (b : UInt64) (x : α) : TA V α :=
  if monomial V op then
    let d := complementBits V b
    single d (x * Coeff.ofRat (unCoeff V op b d))
  else match Kernel.unTermsC V op b with
    | .ok #[] => single (complementBits V b) (x * Coeff.zero)
    | .ok ts => ts.foldl (fun acc t => acc + single t.bits (x * Coeff.ofRat t.coef)) zero
    | .error _ => zero

/-- A term's image under `metric`/`antimetric`: a `Single` on the same blade (in a
non-diagonal space, the sum of the Gram images). -/
def metricTerm (op : UnOp) (b : UInt64) (x : α) : TA V α :=
  if monomial V op then single b (x * Coeff.ofRat (unCoeff V op b b))
  else match Kernel.unTermsC V op b with
    | .ok ts => ts.foldl (fun acc t => acc + single t.bits (x * Coeff.ofRat t.coef)) zero
    | .error _ => zero

/-- A complement-type map (`complementright`, `complementleft`, `hodge`,
`complementlefthodge`) with Julia's kinds (`src/products.jl:1324-1487`). -/
def complementMap (op : UnOp) : TA V α → TA V α
  | zero => zero
  | infinity => infinity
  | one => compTerm op 0 Coeff.one
  | blade b => compTerm op b Coeff.one
  | single b x => compTerm op b x
  | chain g c => chain (V.n - g) (chainMap op (V.n - g) c)
  | spinor h => ofHalf (halfMap op (V.n % 2 == 1) h)
  | cospinor h => ofHalf (halfMap op (V.n % 2 == 0) h)
  | multi m => multi (multiMap op m)
  | couple b re im => topSingle re + compTerm op b im
  | pseudo b re im => compTerm op (pseudoBits V) im + compTerm op b re
  | phasor .. => panic! "TA.complementMap: complexify a Phasor first (Julia `complexify`)"

/-- Julia `complementright(x)` (`!x`). -/
@[inline] def complementright (x : TA V α) : TA V α := complementMap .complementright x
/-- Julia `complementleft(x)`. -/
@[inline] def complementleft (x : TA V α) : TA V α := complementMap .complementleft x
/-- Julia `hodge(x)` (`⋆x`, `complementrighthodge`). -/
@[inline] def hodge (x : TA V α) : TA V α := complementMap .complementrighthodge x
/-- Julia `complementlefthodge(x)`. -/
@[inline] def complementlefthodge (x : TA V α) : TA V α := complementMap .complementlefthodge x

/-- `metric`/`antimetric` with Julia's kinds (`src/products.jl:1630-1815`). -/
def metricMap (op : UnOp) : TA V α → TA V α
  | zero => zero
  | infinity => infinity
  | one => metricTerm op 0 Coeff.one
  | blade b => metricTerm op b Coeff.one
  | single b x => metricTerm op b x
  | chain g c => chain g (chainMap op g c)
  | spinor h => spinor (halfMap op false h)
  | cospinor h => cospinor (halfMap op true h)
  | multi m => multi (multiMap op m)
  | couple b re im => metricTerm op 0 re + metricTerm op b im
  | pseudo b re im => metricTerm op b re + metricTerm op (pseudoBits V) im
  | phasor .. => panic! "TA.metricMap: complexify a Phasor first (Julia `complexify`)"

/-- Julia `metric(x)`. -/
@[inline] def metric (x : TA V α) : TA V α := metricMap .metric x
/-- Julia `antimetric(x)` (`cometric`). -/
@[inline] def antimetric (x : TA V α) : TA V α := metricMap .antimetric x

/-! ## Grade projections -/

/-- Julia `grade(x, G)` / `x(G)`: the grade-`G` part with Julia's kinds (graded elements
give themselves or `Zero`, a multivector a `Chain`, a half the `Chain` of a grade of its
parity and `Zero` otherwise, a couple its term of grade `G`). -/
def gradeProj (G : Nat) : TA V α → TA V α
  | zero => zero
  | infinity => if G == 0 then infinity else zero
  | one => if G == 0 then one else zero
  | blade b => if popcount b == G then blade b else zero
  | single b x => if popcount b == G then single b x else zero
  | chain g c => if g == G then chain g c else zero
  | spinor h => if G % 2 == 0 && G ≤ V.n then halfGrade h G else zero
  | cospinor h => if G % 2 == 1 && G ≤ V.n then halfGrade h G else zero
  | multi m => multiGrade m G
  | couple b re im =>
    if popcount b == G then single b im else if G == 0 then single 0 re else zero
  | pseudo b re im =>
    if popcount b == G then single b re else if G == V.n then topSingle im else zero
  | phasor .. => zero

/-- Julia `scalar(x)` (`src/multivectors.jl:1107-1112`): the scalar part as a `Single`
(a scalar term or `∞` is itself). -/
def scalar : TA V α → TA V α
  | chain 0 c => single 0 (getD c.v 0)
  | multi m => single 0 (getD m.v 0)
  | spinor h => single 0 (getD h.v 0)
  | couple _ re _ => single 0 re
  | pseudo b re _ => if b == 0 then single 0 re else zero
  | x => gradeProj 0 x

/-- Julia `vector`, `bivector`, `trivector` (`src/multivectors.jl:1113-1125`, `G = 1, 2, 3`). -/
def partProj (G : Nat) : TA V α → TA V α
  | couple b _ im => if popcount b == G then single b im else zero
  | pseudo b re im =>
    if popcount b == G then single b re else if V.grade == G then topSingle im else zero
  | x => gradeProj G x

/-- Julia `vector(x)`. -/
@[inline] def vector (x : TA V α) : TA V α := partProj 1 x
/-- Julia `bivector(x)`. -/
@[inline] def bivector (x : TA V α) : TA V α := partProj 2 x
/-- Julia `trivector(x)` (Julia's `trivector(::Couple)` calls an undefined `imaginarya`). -/
@[inline] def trivector (x : TA V α) : TA V α := partProj 3 x

/-- Julia `volume(x)` / `pseudoscalar(x)` (`src/multivectors.jl:1126-1135`): the top-grade
part as a `Single` (a top blade is itself). -/
def volume : TA V α → TA V α
  | chain g c => if g == V.n then topSingle (getD c.v 0) else zero
  | multi m => topSingle (lastCoeff m.v)
  | spinor h => if V.n % 2 == 0 then topSingle (lastCoeff h.v) else zero
  | cospinor h => if V.n % 2 == 1 then topSingle (lastCoeff h.v) else zero
  | couple b _ im => if popcount b == V.grade then single b im else zero
  | pseudo _ _ im => topSingle im
  | x => gradeProj V.n x

/-! ## Parity and reality parts -/

/-- Julia `even(x)` (`src/parity.jl:479-496`, `src/products.jl:1488-1522`). -/
def even : TA V α → TA V α
  | spinor h => spinor h
  | cospinor _ => zero
  | couple b re im => if popcount b % 2 == 0 then couple b re im else single 0 re
  | pseudo b re im =>
    (if popcount b % 2 == 0 then single b re else zero) +
      (if V.n % 2 == 0 then topSingle im else zero)
  | multi m =>
    if V.n == 2 then single 0 (getD m.v 0) + topSingle (lastCoeff m.v) else spinor (m.half false)
  | phasor .. => panic! "TA.even: complexify a Phasor first (Julia `complexify`)"
  | x => match x.grade? with
    | some g => if g % 2 == 0 then x else zero
    | none => x

/-- Julia `odd(x)`. -/
def odd : TA V α → TA V α
  | spinor _ => zero
  | cospinor h => cospinor h
  | couple b _ im => if popcount b % 2 == 1 then single b im else zero
  | pseudo b re im =>
    (if popcount b % 2 == 1 then single b re else zero) +
      (if V.n % 2 == 1 then topSingle im else zero)
  | multi m => if V.n == 2 then multiGrade m 1 else cospinor (m.half true)
  | phasor .. => panic! "TA.odd: complexify a Phasor first (Julia `complexify`)"
  | x => match x.grade? with
    | some g => if g % 2 == 1 then x else zero
    | none => x

/-- Julia `real(x)` (`src/parity.jl:503-521, 540-550`): the grades fixed by the reverse. -/
def realPart : TA V α → TA V α
  | couple b re im => single 0 re + (if reverseFlips (popcount b) then zero else single b im)
  | pseudo b re im =>
    (if reverseFlips V.n then zero else topSingle im) +
      (if reverseFlips (popcount b) then zero else single b re)
  | multi m => if V.n == 1 then multi m else multi (multiKeep (!reverseFlips ·) m)
  | spinor h =>
    if V.n == 2 || V.n == 3 then single 0 (getD h.v 0)
    else if V.n == 4 then single 0 (getD h.v 0) + topSingle (lastCoeff h.v)
    else spinor (halfKeep (!reverseFlips ·) h)
  | cospinor h =>
    if V.n == 2 then cospinor h
    else if V.n == 3 || V.n == 4 then halfGrade h 1
    else cospinor (halfKeep (!reverseFlips ·) h)
  | phasor .. => panic! "TA.realPart: complexify a Phasor first (Julia `complexify`)"
  | x => match x.grade? with
    | some g => if reverseFlips g then zero else x
    | none => x

/-- Julia `imag(x)`: the grades negated by the reverse. -/
def imagPart : TA V α → TA V α
  | couple b _ im => if reverseFlips (popcount b) then single b im else zero
  | pseudo b re im =>
    (if reverseFlips V.n then topSingle im else zero) +
      (if reverseFlips (popcount b) then single b re else zero)
  | multi m =>
    if V.n == 1 then zero else if V.n == 2 then topSingle (lastCoeff m.v)
    else multi (multiKeep reverseFlips m)
  | spinor h =>
    if V.n == 2 then topSingle (lastCoeff h.v)
    else if V.n == 3 || V.n == 4 || V.n == 5 then halfGrade h 2
    else spinor (halfKeep reverseFlips h)
  | cospinor h =>
    if V.n == 2 then zero
    else if V.n == 3 then topSingle (lastCoeff h.v)
    else if V.n == 4 || V.n == 5 || V.n == 6 then halfGrade h 3
    else cospinor (halfKeep reverseFlips h)
  | phasor .. => panic! "TA.imagPart: complexify a Phasor first (Julia `complexify`)"
  | x => match x.grade? with
    | some g => if reverseFlips g then x else zero
    | none => x

/-! ## Spaces -/

/-- Reinterpret an element in a space `W` with the same blades (Julia `adjoint` moves an
element to the dual space `V'`, `src/products.jl:943-1070`; real coefficients are kept,
`conj` is applied to them). Chains, halves and multivectors must have matching storage
sizes; `none` otherwise. -/
def retarget (W : TensorBundle) (conj : α → α) : TA V α → Option (TA W α)
  | zero => some .zero
  | one => some .one
  | infinity => some .infinity
  | blade b => some (.blade b)
  | single b x => some (.single b (conj x))
  | couple b re im => some (.couple b (conj re) (conj im))
  | pseudo b re im => some (.pseudo b (conj re) (conj im))
  | chain g c =>
    if h : Leibniz.binomial V.n g = Leibniz.binomial W.n g then some (.chain g ⟨(c.v.map conj).cast h⟩) else none
  | spinor s =>
    if h : halfDim V.n false = halfDim W.n false then some (.spinor ⟨(s.v.map conj).cast h⟩) else none
  | cospinor s =>
    if h : halfDim V.n true = halfDim W.n true then some (.cospinor ⟨(s.v.map conj).cast h⟩) else none
  | multi m => if h : 2 ^ V.n = 2 ^ W.n then some (.multi ⟨(m.v.map conj).cast h⟩) else none
  | phasor .. => none

end TA

end Grassmann
