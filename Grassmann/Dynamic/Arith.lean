/-
Julia's `+`/`-` representation lattice on the dynamic layer
(port-notes/grassmann-types.md §4.5, grassmann-products.md §4.10; Grassmann.jl
`src/algebra.jl:744-1140` (`adder`), `src/products.jl:379-941` (`plus`/`minus`)).

`a + b` follows Julia's method dispatch branch by branch, so the result has
Julia's *kind*: `v₁ + v₂` is a `Chain`, `1 + v₁₂` a `Couple`, `Chain{0} + Chain{2}` a
`Spinor`, `v₁ + I` a `PseudoCouple`, a sum in a conformal or tangent space never a
`Couple`. The entries are computed with Julia's arithmetic in Julia's order (entries
that Julia copies are copied, entries it sets are set, entries it adds are added),
so `Float` results agree bit for bit, signed zeros included. The dense value of
every branch is proved to be the sum of the dense values (`Grassmann.Dynamic.Laws`).

`a - b` is `a + (-b)`. Julia's `minus` mirrors `plus` method by method and every
committed golden has the same result kind for `a - b` as for `a + (-b)`; in IEEE
arithmetic `x - y` *is* `x + (-y)`, so this is also bit-exact. It fixes two
documented Julia value bugs (oracle `defects.json`):

* `pseudocouple-addsub` (`src/products.jl:558`): `PseudoCouple ± PseudoCouple` with the
  same blade uses `imagvalue(b)` in the real part; here it is componentwise;
* `chain-minus-term-swap` (`src/algebra.jl:781-900`, `swap = true`): `Chain{0} - term`
  and `Chain{n} - term` add the term;

and the `subamnifold-typo` (`src/products.jl:651`): `term + PseudoCouple` throws
whenever the term's blade is not `B`; here it follows the intended code (the
`minus` sibling), i.e. `I` adds to the pseudoscalar part.

Julia's numbers in sums (`src/products.jl:852-859`): `x + n = x` when `n` is zero,
else `x + n·One(V)`; `n + x = +x` (resp. `n·One(V) + x`); `n - x = -x` (resp.
`n·One(V) - x`) — `addNum`, `numAdd`, `subNum`, `numSub`.

Phasors: Julia evaluates `Phasor ± x` through `complexify` (an exponential), which
a `Coeff` type does not have; these sums are rejected (`panic!`) and must be
complexified first.
-/
import Grassmann.Dynamic.Basic
import Grassmann.Algebra.Arith

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α]

/-! ## Julia-exact in-place additions -/

/-- `c` with `x` added to the entry of blade `X` (Julia `adder`: every other entry is
copied, `c_X + x` at `X`, `src/algebra.jl:781-805`). -/
@[inline] def chainAddAt {g : Nat} (c : Chain V g α) (X : UInt64) (x : α) : Chain V g α :=
  Chain.ofFn fun j => if (Leibniz.indexBasis V.n g)[j.1]! == X then c.v.get j + x else c.v.get j

/-- `h` with `x` added to the entry of blade `X`. -/
@[inline] def halfAddAt {p : Bool} (h : Half V p α) (X : UInt64) (x : α) : Half V p α :=
  Half.ofFn fun j => if ((halfLayout p).blades V.n)[j.1]! == X then h.v.get j + x else h.v.get j

/-- `m` with `x` added to the entry of blade `X`. -/
@[inline] def multiAddAt (m : Multivector V α) (X : UInt64) (x : α) : Multivector V α :=
  Multivector.ofFn fun i => if fullBlade V.n i.1 == X then m.v.get i + x else m.v.get i

/-- The coefficient function of two terms on distinct blades (Julia `adder` sets both
entries of a fresh zero container, `src/algebra.jl:760-779`). -/
@[inline] def twoTerms (A : UInt64) (x : α) (B : UInt64) (y : α) (β : UInt64) : α :=
  if β == A then x else if β == B then y else Coeff.zero

/-! ## Terms, chains, halves and multivectors -/

/-- Julia `adder(a::TensorTerm{V,L}, b::TensorTerm{V,G})` (`src/algebra.jl:747-780`):
the sum of the terms `x·e_A` and `y·e_B`. -/
def addTermTerm (A : UInt64) (x : α) (B : UInt64) (y : α) : TA V α :=
  let L := popcount A
  let G := popcount B
  let ok := coupleOK V
  if A == B then single A (x + y)
  else if ok && L == 0 then couple B x y
  else if ok && G == 0 then couple A y x
  else if ok && L == V.grade then pseudo B y x
  else if ok && G == V.grade then pseudo A x y
  else if L == G then chain L (chainOf V L (twoTerms A x B y))
  else if L % 2 == 0 && G % 2 == 0 then spinor (halfOf V false (twoTerms A x B y))
  else if L % 2 == 1 && G % 2 == 1 then cospinor (halfOf V true (twoTerms A x B y))
  else multi (multiOf V (twoTerms A x B y))

/-- Julia `adder(a::TensorTerm{V,L}, b::Chain{V,G})` (`src/algebra.jl:781-900`): the sum
of the term `x·e_A` and a grade-`G` chain. -/
def addTermChain (A : UInt64) (x : α) {G : Nat} (c : Chain V G α) : TA V α :=
  let L := popcount A
  let ok := coupleOK V
  if L == G then chain G (chainAddAt c A x)
  else if ok && L == 0 && G == V.n then couple (pseudoBits V) x (getD c.v 0)
  else if ok && G == 0 then couple A (getD c.v 0) x
  else if ok && G == V.grade then pseudo A x (getD c.v 0)
  else if L % 2 == 0 && G % 2 == 0 then
    spinor (halfOf V false fun β => if β == A then x else c.coeff β)
  else if L % 2 == 1 && G % 2 == 1 then
    cospinor (halfOf V true fun β => if β == A then x else c.coeff β)
  else multi (multiOf V fun β => if β == A then x else c.coeff β)

/-- Julia `plus(a::TensorTerm, b)` for a container `b` (`src/algebra.jl:781-1040`;
`plus(b::Chain, a::TensorTerm) = plus(a, b)` and likewise for the other containers,
`src/products.jl:504-513`): a term plus a chain, half or multivector. -/
def addTermX (A : UInt64) (x : α) (b : TA V α) : TA V α :=
  match b with
  | chain _ c => addTermChain A x c
  | multi m => multi (multiAddAt m A x)
  | spinor s =>
    if popcount A % 2 == 0 then spinor (halfAddAt s A x)
    else multi (multiAddAt (toMultivector s) A x)
  | cospinor s =>
    if popcount A % 2 == 1 then cospinor (halfAddAt s A x)
    else multi (multiAddAt (toMultivector s) A x)
  | _ => multi (multiAddAt b.toDense A x)

/-- The sum of two halves of parities `p`, `q`: a half when they agree, else
`Multivector(a) + Multivector(b)` (`src/products.jl:566-567`). -/
def addHalves {p q : Bool} (a : Half V p α) (b : Half V q α) : TA V α :=
  if h : p = q then ofHalf (a.cast h + b)
  else multi (toMultivector a + toMultivector b)

/-- Julia `plus(a::Chain{V,G}, b::Chain{V,L})` (`src/products.jl:876-886`): equal grades
add; a scalar or pseudoscalar chain is first made a term (`Single(·)`); chains of one
parity add as halves (`multispin`); otherwise as multivectors. -/
def addChains {G L : Nat} (a : Chain V G α) (b : Chain V L α) : TA V α :=
  if h : G = L then chain L (a.cast h + b)
  else if G == 0 || G == V.n then
    match singleOfChain a with
    | single A x => addTermChain A x b
    | _ => multi (toMultivector a + toMultivector b)
  else if L == 0 || L == V.n then
    match singleOfChain b with
    | single B y => addTermChain B y a
    | _ => multi (toMultivector a + toMultivector b)
  else if G % 2 == L % 2 then addHalves (Half.ofChain a) (Half.ofChain b)
  else multi (toMultivector a + toMultivector b)

/-- Sums of two containers (chains, halves, multivectors; `src/products.jl:860-941`). -/
def addXX (a b : TA V α) : TA V α :=
  match a, b with
  | chain _ c, chain _ d => addChains c d
  | chain G c, spinor s =>
    if G % 2 == 0 then addHalves (Half.ofChain c) s else multi (toMultivector c + toMultivector s)
  | spinor s, chain G c =>
    if G % 2 == 0 then addHalves s (Half.ofChain c) else multi (toMultivector s + toMultivector c)
  | chain G c, cospinor s =>
    if G % 2 == 1 then addHalves (Half.ofChain c) s else multi (toMultivector c + toMultivector s)
  | cospinor s, chain G c =>
    if G % 2 == 1 then addHalves s (Half.ofChain c) else multi (toMultivector s + toMultivector c)
  | spinor s, spinor t => spinor (s + t)
  | cospinor s, cospinor t => cospinor (s + t)
  | multi m, multi w => multi (m + w)
  | _, _ => multi (a.toDense + b.toDense)

/-- The lattice on terms and containers (no zero, infinity, couples or phasors). -/
def addB (a b : TA V α) : TA V α :=
  match a.term?, b.term? with
  | some (A, x), some (B, y) => addTermTerm A x B y
  | some (A, x), none => addTermX A x b
  | none, some (B, y) => addTermX B y a
  | none, none => addXX a b

/-! ## Couples and pseudo-couples with terms -/

/-- Julia `plus(a::Couple{V,B}, b::TensorTerm)` (`src/products.jl:632-647`): a scalar term
or a term on `B` stays in the couple; otherwise `multispin(a) + b`. -/
def addCoupleTerm (B : UInt64) (re im : α) (C : UInt64) (y : α) : TA V α :=
  if C == 0 then couple B (re + y) im
  else if C == B then couple B re (im + y)
  else addB (multispin (couple B re im)) (single C y)

/-- Julia `plus(a::TensorTerm, b::Couple{V,B})` (`src/products.jl:632-647`). -/
def addTermCouple (C : UInt64) (y : α) (B : UInt64) (re im : α) : TA V α :=
  if C == 0 then couple B (y + re) im
  else if C == B then couple B re (y + im)
  else addB (single C y) (multispin (couple B re im))

/-- Julia `plus(a::PseudoCouple{V,B}, b::TensorTerm)` (`src/products.jl:656-664`): a term
on `B` or on `I` stays in the pseudo-couple; otherwise `multispin(a) + b`. -/
def addPseudoTerm (B : UInt64) (re im : α) (C : UInt64) (y : α) : TA V α :=
  if C == B then pseudo B (re + y) im
  else if C == pseudoBits V then pseudo B re (im + y)
  else addB (multispin (pseudo B re im)) (single C y)

/-- Julia `plus(a::TensorTerm, b::PseudoCouple{V,B})` (`src/products.jl:648-655`, with
the intended `Submanifold(V)` for the `Subamnifold` typo). -/
def addTermPseudo (C : UInt64) (y : α) (B : UInt64) (re im : α) : TA V α :=
  if C == B then pseudo B (y + re) im
  else if C == pseudoBits V then pseudo B re (y + im)
  else addB (single C y) (multispin (pseudo B re im))

/-- The lattice extended by couples and pseudo-couples meeting terms. -/
def addL1 (a b : TA V α) : TA V α :=
  match a, b with
  | couple B re im, _ => match b.term? with
    | some (C, y) => addCoupleTerm B re im C y
    | none => addB (multispin a) b
  | pseudo B re im, _ => match b.term? with
    | some (C, y) => addPseudoTerm B re im C y
    | none => addB (multispin a) b
  | _, couple B re im => match a.term? with
    | some (C, y) => addTermCouple C y B re im
    | none => addB a (multispin b)
  | _, pseudo B re im => match a.term? with
    | some (C, y) => addTermPseudo C y B re im
    | none => addB a (multispin b)
  | _, _ => addB a b

/-! ## The full lattice -/

/-- Julia `a + b` on dynamic elements (the representation lattice of
grassmann-types.md §4.5). -/
def add (a b : TA V α) : TA V α :=
  match a, b with
  | zero, _ => b
  | _, zero => a
  | infinity, _ => infinity
  | _, infinity => infinity
  | phasor .., _ => panic! "TA.add: complexify a Phasor before adding it (Julia `complexify`)"
  | _, phasor .. => panic! "TA.add: complexify a Phasor before adding it (Julia `complexify`)"
  -- couples with couples (`src/products.jl:555-569`)
  | couple B r i, couple C s j =>
    if B == C then couple B (r + s) (i + j) else addL1 (addL1 a (coupleScalar s)) (termOf C j)
  | pseudo B r i, pseudo C s j =>
    if B == C then pseudo B (r + s) (i + j) else addL1 (addL1 a (pseudoVolume j)) (termOf C s)
  | couple .., pseudo C s j => addL1 (addL1 a (termOf C s)) (pseudoVolume j)
  | pseudo B r i, couple .. => addL1 (addL1 (termOf B r) b) (pseudoVolume i)
  -- couples with chains (`src/products.jl:530-553`): `Chain{V,0}` goes through the scalar
  | couple B r i, chain g _ =>
    if g == 0 then addL1 (addB b (coupleScalar r)) (termOf B i)
    else addL1 (addB b (termOf B i)) (coupleScalar r)
  | chain g _, couple C s j =>
    if g == 0 then addL1 (addB a (coupleScalar s)) (termOf C j)
    else addL1 (addB a (termOf C j)) (coupleScalar s)
  | pseudo B r i, chain g _ =>
    if g == 0 then addL1 (addB b (pseudoVolume i)) (termOf B r)
    else addL1 (addB b (termOf B r)) (pseudoVolume i)
  | chain g _, pseudo C s j =>
    if g == 0 then addL1 (addB a (pseudoVolume j)) (termOf C s)
    else addL1 (addB a (termOf C s)) (pseudoVolume j)
  -- couples with halves and multivectors
  | couple B r i, spinor _ | couple B r i, cospinor _ | couple B r i, multi _ =>
    addL1 (addB b (coupleScalar r)) (termOf B i)
  | spinor _, couple C s j | cospinor _, couple C s j | multi _, couple C s j =>
    addL1 (addB a (coupleScalar s)) (termOf C j)
  | pseudo B r i, spinor _ | pseudo B r i, cospinor _ | pseudo B r i, multi _ =>
    addL1 (addB b (pseudoVolume i)) (termOf B r)
  | spinor _, pseudo C s j | cospinor _, pseudo C s j | multi _, pseudo C s j =>
    addL1 (addB a (pseudoVolume j)) (termOf C s)
  -- couples with terms, and everything else
  | _, _ => addL1 a b

/-! ## Negation and scalars -/

/-- Julia `-x` (`src/products.jl:514-520`): a unit blade becomes `Single(-1, b)`, the
containers negate their values; `-Zero = Zero` and `-∞ = ∞` (Julia has no method:
defects `zero-method-gaps`, `infinity-method-gaps`); `-Phasor = Phasor(-amp, angle)`. -/
def neg : TA V α → TA V α
  | zero => zero
  | one => single 0 (-Coeff.one)
  | infinity => infinity
  | blade b => single b (-Coeff.one)
  | single b x => single b (-x)
  | chain g c => chain g (-c)
  | couple b re im => couple b (-re) (-im)
  | pseudo b re im => pseudo b (-re) (-im)
  | spinor s => spinor (-s)
  | cospinor s => cospinor (-s)
  | multi m => multi (-m)
  | phasor amp θ => phasor (-amp) θ

/-- Julia `s * x` for a scalar `s` (`src/products.jl:830-851, 1093-1112`): the kind is
kept, a unit blade becomes a `Single`; `s * Zero = Zero`, `s * ∞ = ∞`. -/
def smul (s : α) : TA V α → TA V α
  | zero => zero
  | one => single 0 s
  | infinity => infinity
  | blade b => single b s
  | single b x => single b (s * x)
  | chain g c => chain g ⟨c.v.map (s * ·)⟩
  | couple b re im => couple b (s * re) (s * im)
  | pseudo b re im => pseudo b (s * re) (s * im)
  | spinor h => spinor ⟨h.v.map (s * ·)⟩
  | cospinor h => cospinor ⟨h.v.map (s * ·)⟩
  | multi m => multi ⟨m.v.map (s * ·)⟩
  | phasor amp θ => phasor (s * amp) θ

/-- Julia `x * s` for a scalar `s` (the scalar on the right). -/
def mulScalar (x : TA V α) (s : α) : TA V α :=
  match x with
  | zero => zero
  | one => single 0 s
  | infinity => infinity
  | blade b => single b s
  | single b v => single b (v * s)
  | chain g c => chain g ⟨c.v.map (· * s)⟩
  | couple b re im => couple b (re * s) (im * s)
  | pseudo b re im => pseudo b (re * s) (im * s)
  | spinor h => spinor ⟨h.v.map (· * s)⟩
  | cospinor h => cospinor ⟨h.v.map (· * s)⟩
  | multi m => multi ⟨m.v.map (· * s)⟩
  | phasor amp θ => phasor (amp * s) θ

/-- Julia `x / s` for a scalar `s` (entrywise division; `Zero/s = Zero`, `∞/s = ∞`). -/
def divScalar [Div α] (x : TA V α) (s : α) : TA V α :=
  match x with
  | zero => zero
  | one => single 0 (Coeff.one / s)
  | infinity => infinity
  | blade b => single b (Coeff.one / s)
  | single b v => single b (v / s)
  | chain g c => chain g ⟨c.v.map (· / s)⟩
  | couple b re im => couple b (re / s) (im / s)
  | pseudo b re im => pseudo b (re / s) (im / s)
  | spinor h => spinor ⟨h.v.map (· / s)⟩
  | cospinor h => cospinor ⟨h.v.map (· / s)⟩
  | multi m => multi ⟨m.v.map (· / s)⟩
  | phasor amp θ => phasor (amp / s) θ

/-- Julia `a - b = a + (-b)` (see the module docstring). -/
@[inline] def sub (a b : TA V α) : TA V α := add a (neg b)

instance : Add (TA V α) := ⟨add⟩
instance : Sub (TA V α) := ⟨sub⟩
instance : Neg (TA V α) := ⟨neg⟩
instance : HMul α (TA V α) (TA V α) := ⟨smul⟩
instance : HMul (TA V α) α (TA V α) := ⟨mulScalar⟩
instance : SMul α (TA V α) := ⟨smul⟩
instance [Div α] : HDiv (TA V α) α (TA V α) := ⟨divScalar⟩

/-! ## Numbers in sums (`src/products.jl:852-859`) -/

/-- Julia `x + n` (`n` a number): `x` itself when `n` is zero, else `x + Single{V}(n)`. -/
def addNum (x : TA V α) (n : α) : TA V α := if Coeff.isZero n then x else x + single 0 n

/-- Julia `n + x`: `+x = x` when `n` is zero, else `Single{V}(n) + x`. -/
def numAdd (n : α) (x : TA V α) : TA V α := if Coeff.isZero n then x else single 0 n + x

/-- Julia `x - n`: `x` when `n` is zero, else `x - Single{V}(n)`. -/
def subNum (x : TA V α) (n : α) : TA V α := if Coeff.isZero n then x else x - single 0 n

/-- Julia `n - x`: `-x` when `n` is zero, else `Single{V}(n) - x`. -/
def numSub (n : α) (x : TA V α) : TA V α := if Coeff.isZero n then -x else single 0 n - x

end TA

end Grassmann
