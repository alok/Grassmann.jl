/-
Products of dynamic elements with Julia's result kinds (Grassmann.jl
`src/algebra.jl:29-300, 1152-1560` (the `product`, `product_∧`, `product_∨`,
`product_contraction` generators), `src/products.jl:379-826, 1146-1320` (dispatch,
couples, `Zero`/`Infinity`); AbstractTensors `src/AbstractTensors.jl:257-265, 349`
(the derived products); port-notes/grassmann-products.md §4.4-4.8).

The four core products `⟑ ∧ ∨ contraction` follow Julia's method dispatch:

* **terms × terms**: DirectSum's blade-level result (`TensorBundle.apply₂`: a blade, a
  `Single`, `Zero`, or in a conformal space a sum of `Single`s), scaled by the product of
  the values (a scaled blade is a `Single`);
* **graded × `Chain`**: Julia's generators, with their early outs (a scalar or
  pseudoscalar factor becomes a term, `⟑` by a pseudoscalar is a Hodge complement, `∧`
  and `∨` beyond the grade range are `Zero`, a conformal contraction is a
  `Multivector`), otherwise `Spinor`/`CoSpinor` (`⟑`) or the `Chain` of the result grade;
* **graded × `Spinor`/`CoSpinor`/`Multivector`**: the generator's grade-range early
  outs (a single grade block of the container, or two), otherwise the container kind of
  Julia's `outype`;
* **containers × containers**: `Multivector` with a multivector, halves by parity (`∨`
  shifted by the parity of `n`);
* **`Couple`/`PseudoCouple`**: Julia's formulas (same blade) and part-by-part
  expansions, summed with the `+` lattice.

Entries are computed by the static kernels (`Kernels.binProj`) into the result
layout, or by Julia's own formulas where Julia uses them (scalar and pseudoscalar
factors). Fixed Julia defects (oracle `defects.json`): `chain0-times-mixed`,
`pseudocouple-mul-diffB`, `contractn-typo`, `vee-scalar-couple-B-unbound`,
`vee-pseudoscalar-couple`, `conformal-blade-complement` (container-level complements).
-/
import Grassmann.Dynamic.Unary
import Grassmann.Algebra.Products
import Grassmann.Dynamic.Loops

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-- The four core products. -/
inductive POp where
  /-- The geometric product `⟑` (`*`). -/
  | mul
  /-- The exterior product `∧`. -/
  | wedge
  /-- The regressive product `∨`. -/
  | vee
  /-- The right contraction (`contraction`, `⋅`, `⨽`). -/
  | contraction
  deriving DecidableEq, Repr, Inhabited

/-- The DirectSum operation of a core product. -/
def POp.bin : POp → BinOp
  | .mul => .mul | .wedge => .wedge | .vee => .vee | .contraction => .contraction

/-! ## Julia's generated loops -/

/-- A term or container as an operand of Julia's generated loops, with its raw storage
(`none` for couples, `Zero`, `∞`, phasors). -/
def loopSrc? (x : TA V α) : Option (Loops.JSrc × Packed.Arr α) :=
  match x with
  | one => some (.terms #[0], Loops.termArr Coeff.one)
  | blade b => some (.terms #[b], Loops.termArr Coeff.one)
  | single b v => some (.terms #[b], Loops.termArr v)
  | chain g c => some (.dense (.chain g), c.v.data)
  | spinor h => some (.dense .even, h.v.data)
  | cospinor h => some (.dense .odd, h.v.data)
  | multi m => some (.dense .full, m.v.data)
  | _ => none

/-- A container of layout `l`. -/
def ofLayout (l : Layout) (v : Values α (l.size V.n)) : TA V α :=
  match l, v with
  | .chain g, v => chain g ⟨v⟩
  | .even, v => spinor ⟨v⟩
  | .odd, v => cospinor ⟨v⟩
  | .full, v => multi ⟨v⟩

/-- The product `op(a, b)` of two terms or containers by Julia's generated loop into
layout `lc` (contributions outside `lc` are dropped: callers choose Julia's layout, which
holds them all); `outerFirst` is the loop nesting, `pre` Julia's expression form (the
generators below their `cache_limit`), see `Grassmann.Loops`. -/
def loopInto (op : POp) (lc : Layout) (outerFirst pre : Bool) (a b : TA V α) : TA V α :=
  match loopSrc? a, loopSrc? b with
  | some (sa, xa), some (sb, xb) =>
    ofLayout lc (Loops.run pre { V, op := op.bin, a := sa, b := sb, lc, outerFirst } xa xb)
  | _, _ => zero

/-- Julia's `cache_limit` (Leibniz `src/utilities.jl:106`): the generators unroll a
graded product when `binomial(n, G)·binomial(n, L) < 2¹²`, a graded × container product
when `n < 12`, a container product when `n < 6`. -/
def cacheLimit : Nat := 12

/-- Whether the graded × `Chain` generator of grades `L` (a chain when `isChain`, else a
term) and `G` takes its expression form. -/
def gradedPre (n L G : Nat) (isChain : Bool) : Bool :=
  (Layout.chain G).size n * (if isChain then (Layout.chain L).size n else 1) < 2 ^ cacheLimit

/-- The half layout of parity `p`. -/
@[inline] def halfL (odd : Bool) : Layout := halfLayout odd

/-! ## Terms -/

/-- A term's blade, value and whether it is a unit blade (Julia `Submanifold`). -/
def termData? : TA V α → Option (UInt64 × α × Bool)
  | one => some (0, Coeff.one, true)
  | blade b => some (b, Coeff.one, true)
  | single b x => some (b, x, false)
  | _ => none

/-- Julia's value-free blade-level result as a dynamic element (`+(Single{V}.(terms)...)`
for a sum). -/
def ofBladeResult : BladeResult → TA V α
  | .zero => zero
  | .blade b => ofBlade b
  | .single c b => single b (Coeff.ofRat c)
  | .sum ts => ts.foldl (fun acc (b, c) => acc + single b (Coeff.ofRat c)) zero
  | .nested .. => zero

/-- The product of two terms (Julia `⟑(::Submanifold, ::Submanifold)`, `v*mul(a, b)`,
`∧`/`∨`/`contraction` of `TensorTerm`s, `src/algebra.jl:29-300`): the blade-level
result, scaled by the product of the values when either term is not a unit blade. -/
def termProd (op : POp) (A : UInt64) (x : α) (ua : Bool) (B : UInt64) (y : α) (ub : Bool) : TA V α :=
  match V.apply₂ op.bin A B with
  | .ok r => if ua && ub then ofBladeResult r else smul (x * y) (ofBladeResult r)
  | .error _ => zero

/-! ## Graded × chain (Julia's `product*` generators, `src/algebra.jl:1152-1450`) -/

/-- The value of a term or scalar chain used as a factor. -/
def scalarOf : TA V α → α
  | single _ x => x
  | chain _ c => getD c.v 0
  | _ => Coeff.one

/-- The product of a graded element `a` (a term or a chain of grade `L`) and a chain `b`
of grade `G`; `swap` evaluates `b ⊙ a` (Julia's `op(b::Chain, a::TensorTerm)`), in which
case `a` is a term. The generated loops run over the first operand outermost. A conformal
chain × chain contraction is a `Multivector` (`μ = istangent(V)|hasconformal(V)`, only in
the unrolled chain × chain branch; a term's contraction stays a `Chain`). -/
def gradedChain (op : POp) (a : TA V α) (L : Nat) {G : Nat} (c : Chain V G α) (swap : Bool) : TA V α :=
  let b : TA V α := chain G c
  let n := V.n
  let tangent := V.istangent
  let isChain := match a with | chain .. => true | _ => false
  let pre := gradedPre n L G isChain
  let loop := fun (lc : Layout) => if swap then loopInto op lc true pre b a else loopInto op lc true pre a b
  -- `Single(b)` of a scalar or pseudoscalar chain
  let sb : TA V α := singleOfChain c
  -- the term product with `Single(b)` in Julia's operand order
  let withSingle := fun (sb : TA V α) => match termData? a, termData? sb with
    | some (A, x, ua), some (B, y, ub) =>
      if swap then termProd op B y ub A x ua else termProd op A x ua B y ub
    | _, _ => zero
  match op with
  | .mul =>
    if G == 0 then
      if isChain then mulScalar a (getD c.v 0) else withSingle sb
    else if isChain && L == 0 then smul (scalarOf a) b
    else if (if swap then L else G) == n && !tangent then
      if swap then
        (match a with
          | single _ x => mulScalar (hodge (reverse b)) x
          | _ => hodge (reverse b))
      else mulScalar (hodge (reverse a)) (getD c.v 0)
    else if (if swap then G else L) == n && !tangent then
      if swap then smul (getD c.v 0) (complementlefthodge (reverse a))
      else match a with
        | single _ x => smul x (complementlefthodge (reverse b))
        | chain _ d => smul (getD d.v 0) (complementlefthodge (reverse b))
        | _ => complementlefthodge (reverse b)
    else loop (halfL ((L + G) % 2 == 1))
  | .wedge =>
    if L + G > n && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent then loop .full
    else loop (.chain (L + G))
  | .vee =>
    if L + G < n && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent then loop .full
    else loop (.chain (L + G - n))
  | .contraction =>
    if (if swap then G < L else L < G) && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent || (V.hasconformal && isChain && pre) then loop .full
    else loop (.chain (if swap then G - L else L - G))

/-- The product of two chains (Julia `op(a::Chain, b::Chain)`): `gradedChain` with the
left chain as the graded factor; a scalar or pseudoscalar right chain becomes a term,
which dispatches to `op(a::Chain, b::TensorTerm)`. -/
def chainChain (op : POp) {L G : Nat} (a : Chain V L α) (c : Chain V G α) : TA V α :=
  let n := V.n
  let tangent := V.istangent
  let redirect := match op with
    | .mul => false
    | .wedge => !(L + G > n && !tangent) && (G == 0 || G == n) && !tangent
    | .vee => !(L + G < n && !tangent) && (G == 0 || G == n) && !tangent
    | .contraction => !(L < G && !tangent) && (G == 0 || G == n) && !tangent
  if redirect then
    -- `op(a, Single(b))` is `op(a::Chain, b::TensorTerm)`: the swapped generator
    gradedChain op (singleOfChain c) G a true
  else if op == .mul && G == 0 then mulScalar (chain L a) (getD c.v 0)
  else gradedChain op (chain L a) L c false

/-! ## Graded × half or multivector (`src/algebra.jl:1450-1560`) -/

/-- Julia's `mingrade`, `maxgrade`, `nextgrade`, `maxpseudograde` of a container
(`src/multivectors.jl:1156-1197`): `(min, max, next, maxpseudo)`, as integers (Julia's
`nextmaxgrade`/`nextmaxpseudograde` can be negative). -/
def gradeRange (V : TensorBundle) : TA V α → Int × Int × Int × Int
  | spinor _ => (0, if V.n % 2 == 1 then V.n - 1 else V.n, 2, V.n)
  | cospinor _ => (1, if V.n % 2 == 1 then V.n else (V.n : Int) - 1, 2, (V.n : Int) - 1)
  | _ => (0, V.n, 1, V.n)

/-- The container kind of Julia's generic loop for `op(a, b)` with a graded `a` of grade
`G` and a container `b` (`outype`). -/
def containerOut (op : POp) (G : Nat) : TA V α → Layout
  | spinor _ => match op with
    | .vee => halfL ((G % 2 == 1) ^^ (V.n % 2 == 1))
    | _ => halfL (G % 2 == 1)
  | cospinor _ => match op with
    | .vee => halfL (!((G % 2 == 1) ^^ (V.n % 2 == 1)))
    | _ => halfL (G % 2 == 0)
  | _ => .full

/-- The product of a graded element `a` (a term or chain of grade `G`) with a half or
multivector `b`; `swap` evaluates `b ⊙ a`. `core` is the core product itself (used on
grade blocks of `b`). Julia's generated loop runs over the container outermost. -/
def gradedContainer (core : POp → TA V α → TA V α → TA V α) (op : POp) (a : TA V α) (G : Nat)
    (b : TA V α) (swap : Bool) : TA V α :=
  let n := V.n
  let N : Int := n
  let g : Int := G
  let tangent := V.istangent
  let (mn, mx, nx, mxp) := gradeRange V b
  let blk := fun (k : Int) => gradeProj k.toNat b
  let app := fun (x : TA V α) => if swap then core op x a else core op a x
  let generic := fun (_ : Unit) =>
    let pre := n < cacheLimit
    if swap then loopInto op (containerOut op G b) true pre b a
    else loopInto op (containerOut op G b) false pre a b
  match op with
  | .mul =>
    match a with
    | chain _ d =>
      if G == 0 then (if swap then mulScalar b (getD d.v 0) else smul (getD d.v 0) b)
      else if G == n && !tangent then
        (if swap then smul (getD d.v 0) (hodge (reverse b))
         else smul (getD d.v 0) (complementlefthodge (reverse b)))
      else generic ()
    | single _ x =>
      if G == n && !tangent then
        (if swap then mulScalar (hodge (reverse b)) x else smul x (complementlefthodge (reverse b)))
      else generic ()
    | _ =>
      if G == n && !tangent then
        (if swap then hodge (reverse b) else complementlefthodge (reverse b))
      else generic ()
  | .wedge =>
    if g + mn > N && !tangent then zero
    else if g + mn == N && !tangent then app (blk mn)
    else if g + (mn + nx) == N && !tangent then app (blk mn) + app (blk (mn + nx))
    else generic ()
  | .vee =>
    if g + mx < N && !tangent then zero
    else if g + mx == N && !tangent then app (blk mx)
    else if g + (mx - nx) == N && !tangent then app (blk mx) + app (blk (mx - nx))
    else generic ()
  | .contraction =>
    if (if swap then mx < g else g < mn) && !tangent then zero
    else if (if swap then mx == g else g + mxp == N) && !tangent then
      (if swap then core op (blk mx) a else core op a (blk mn))
    else if (if swap then mx - nx == g else g + (mxp - nx) == N) && !tangent then
      (if swap then core op (blk mx) a + core op (blk (mx - nx)) a
       else core op a (blk mn) + core op a (blk (mn + nx)))
    else generic ()

/-- The product of two containers (halves and multivectors; `src/products.jl:1146-1320`,
the loop over the first operand outermost). -/
def containerContainer (op : POp) (a b : TA V α) : TA V α :=
  let parity := fun (x : TA V α) => match x with
    | spinor _ => some false
    | cospinor _ => some true
    | _ => none
  let pre := 2 * V.n < cacheLimit
  match parity a, parity b with
  | some p, some q =>
    let r := p ^^ q
    let r := if op == .vee then r ^^ (V.n % 2 == 1) else r
    loopInto op (halfL r) true pre a b
  | _, _ => loopInto op .full true pre a b

/-! ## The core products -/

/-- The core products of terms and containers (no couples). -/
def baseProd (op : POp) (a b : TA V α) : TA V α :=
  match a, b with
  | zero, _ | _, zero => zero
  | infinity, _ | _, infinity => infinity
  | phasor .., _ | _, phasor .. => panic! "TA product: complexify a Phasor first (Julia `complexify`)"
  | _, _ =>
    match termData? a, termData? b with
    | some (A, x, ua), some (B, y, ub) => termProd op A x ua B y ub
    | _, _ =>
      match a, b with
      -- Julia's scalar shortcuts (`src/products.jl:521-524`)
      | one, chain _ c => if op == .mul then chain _ c else gradedChain op one 0 c false
      | chain _ c, one => if op == .mul then chain _ c else gradedChain op one 0 c true
      | single 0 x, chain _ c =>
        if op == .mul then chain _ ⟨c.v.map (x * ·)⟩ else gradedChain op a 0 c false
      | chain _ c, single 0 y =>
        if op == .mul then chain _ ⟨c.v.map (· * y)⟩ else gradedChain op b 0 c true
      | chain _ c, chain _ d => chainChain op c d
      | chain g c, _ =>
        match termData? b with
        | some (B, _, _) => gradedChain op b (popcount B) c true
        | none => gradedContainer baseProdNC op a g b false
      | _, chain g c =>
        match termData? a with
        | some (A, _, _) => gradedChain op a (popcount A) c false
        | none => gradedContainer baseProdNC op b g a true
      | _, _ =>
        match termData? a, termData? b with
        | some (A, _, _), none => gradedContainer baseProdNC op a (popcount A) b false
        | none, some (B, _, _) => gradedContainer baseProdNC op b (popcount B) a true
        | _, _ => containerContainer op a b
where
  /-- Products of a term or chain with a grade block (the early outs of the container
  generator only ever pair a graded element with a chain). -/
  baseProdNC (op : POp) (x y : TA V α) : TA V α :=
    match x, y with
    | zero, _ | _, zero => zero
    | chain _ c, chain _ d => chainChain op c d
    | chain _ c, _ => match termData? y with
      | some (B, _, _) => gradedChain op y (popcount B) c true
      | none => zero
    | _, chain _ d => match termData? x with
      | some (A, _, _) => gradedChain op x (popcount A) d false
      | none => zero
    | _, _ => match termData? x, termData? y with
      | some (A, a1, ua), some (B, b1, ub) => termProd op A a1 ua B b1 ub
      | _, _ => zero

/-! ## Couples and pseudo-couples (`src/products.jl:571-826`) -/

/-- The scalar coefficient of the blade product `op(A, B)` (Julia `value(op(B, B))`,
`value(abs2_inv(B))`). -/
def scalarCoef (V : TensorBundle) (op : BinOp) (A B : UInt64) : Rat :=
  match V.terms₂ op A B with
  | .ok ts => (ts.find? fun t => t.bits == 0 && t.z == 0).map (·.coef) |>.getD 0
  | .error _ => 0

/-- Whether an element is a scalar term (Julia `TensorTerm{V,0}`), with its value. -/
def scalarTerm? (x : TA V α) : Option α :=
  match termData? x with
  | some (0, v, _) => some v
  | _ => none

/-- A `Couple` result `re + value(out)·basis(out)` of Julia's same-blade
`PseudoCouple` formulas. -/
def coupleOf (re : α) (out : TA V α) : TA V α :=
  match out with
  | single b v => couple b re v
  | blade b => couple b re Coeff.one
  | zero => couple 0 re Coeff.zero  -- `basis(Zero(V)) = One(V)`, `value(Zero(V)) = 0`
  | _ => single 0 re + out

/-- `z ⟑ t` and `t ⟑ z` for a couple or pseudo-couple `z = (B, re, im)` and a term or
container `t`: a scalar term scales both parts (`src/products.jl:721-724`), a scalar or
pseudoscalar chain is first made a term, anything else distributes over the parts
(`first` is the part Julia multiplies first: the scalar of a couple, the volume of a
pseudo-couple). -/
def mulParts (pseudo? : Bool) (B : UInt64) (re im : α) (t : TA V α) (left : Bool) : TA V α :=
  let rebuild := fun (r i : α) => if pseudo? then pseudo B r i else couple B r i
  let first : TA V α := if pseudo? then topSingle im else single 0 re
  let second : TA V α := if pseudo? then single B re else single B im
  let dist := fun (t : TA V α) =>
    if left then baseProd .mul first t + baseProd .mul second t
    else baseProd .mul t first + baseProd .mul t second
  let t := match t with
    | chain g c => if g == 0 || g == V.n then singleOfChain c else t
    | _ => t
  match scalarTerm? t with
  | some v => if left then rebuild (re * v) (im * v) else rebuild (v * re) (v * im)
  | none => dist t

/-- A product with a `Couple`/`PseudoCouple` on one side and a term or container on the
other (Julia's part-by-part methods, `src/products.jl:705-826`). -/
def prodTC (op : POp) (a b : TA V α) : TA V α :=
  let bp := baseProd op
  let sa := scalarTerm? a
  let sb := scalarTerm? b
  let n := V.n
  let isTop := fun (x : TA V α) => match termData? x with
    | some (A, _, _) => A == pseudoBits V
    | none => false
  let blade? := fun (x : TA V α) => (termData? x).map (·.1)
  let isTerm := (termData? a).isSome || (termData? b).isSome
  match a, b with
  | zero, _ | _, zero => zero
  | infinity, _ | _, infinity => infinity
  -- a couple on the left
  | couple B r i, _ =>
    let cs : TA V α := single 0 r
    let ci : TA V α := single B i
    match op with
    | .mul => mulParts false B r i b true
    | .wedge =>
      match sb with
      | some _ => mulParts false B r i b true
      | none => if isTerm && blade? b == some B then bp cs b else bp cs b + bp ci b
    | .vee =>
      match sb with
      | some _ => if popcount B == n then bp ci b else zero
      | none => if isTerm && not (isTop b) then bp ci b else bp cs b + bp ci b
    | .contraction =>
      match sb with
      | some _ => mulParts false B r i b true
      | none => if isTerm && B != 0 then bp ci b else bp cs b + bp ci b
  -- a pseudo-couple on the left
  | pseudo B r i, _ =>
    let pi : TA V α := single B r
    let pv : TA V α := topSingle i
    match op with
    | .mul => mulParts true B r i b true
    | .wedge =>
      match sb with
      | some _ => mulParts true B r i b true
      | none => if isTerm then (if blade? b == some B then zero else bp pi b) else bp pv b + bp pi b
    | .vee =>
      match sb with
      | some _ => bp pv b
      | none => if isTerm then bp pi b + bp pv b else bp pv b + bp pi b
    | .contraction =>
      match sb with
      | some _ => mulParts true B r i b true
      | none => bp pi b + bp pv b
  -- a couple on the right
  | _, couple B r i =>
    let cs : TA V α := single 0 r
    let ci : TA V α := single B i
    match op with
    | .mul => mulParts false B r i a false
    | .wedge =>
      match sa with
      | some _ => mulParts false B r i a false
      | none => if isTerm && blade? a == some B then bp a cs else bp a cs + bp a ci
    | .vee =>
      match sa with
      | some _ => if popcount B == n then bp a ci else zero
      | none => if isTerm && not (isTop a) then bp a ci else bp a cs + bp a ci
    | .contraction =>
      match sa with
      | some v => single 0 (v * r)
      | none => bp a cs + bp a ci
  -- a pseudo-couple on the right
  | _, pseudo B r i =>
    let pi : TA V α := single B r
    let pv : TA V α := topSingle i
    match op with
    | .mul => mulParts true B r i a false
    | .wedge =>
      match sa with
      | some _ => mulParts true B r i a false
      | none => if isTerm then (if blade? a == some B then zero else bp a pi) else bp a pv + bp a pi
    | .vee =>
      match sa with
      | some _ => bp a pv
      | none => if isTerm then bp a pi + bp a pv else bp a pv + bp a pi
    | .contraction =>
      match sa with
      | some _ => bp a pi
      | none => if isTerm then (if isTop a then bp a pi + bp a pv else bp a pi) else bp a pv + bp a pi
  | _, _ => bp a b

/-- The core product `op(a, b)` of any two dynamic elements, with Julia's result kind
(couples with couples by Julia's same-blade formulas or part by part,
`src/products.jl:571-704`). -/
def prod (op : POp) (a b : TA V α) : TA V α :=
  let tc := prodTC op
  match a, b with
  | couple B r i, couple C s j =>
    let cs : TA V α := single 0 s
    let ci : TA V α := single C j
    match op with
    | .mul =>
      if B == C then couple B (r * s + i * j * Coeff.ofRat (scalarCoef V .mul B B)) (r * j + i * s)
      else tc a cs + tc a ci
    | .wedge => if B == C then couple B (r * s) (r * j + i * s) else tc a cs + tc a ci
    | .vee =>
      if B == C then (if popcount B == V.n then couple B (r * j + i * s) (i * j) else zero)
      else tc (single 0 r) b + tc (single B i) b
    | .contraction =>
      if B == C then couple B (r * s + i * j * Coeff.ofRat (scalarCoef V .contraction B B)) (i * s)
      else tc a ci + tc a cs
  | pseudo B r i, pseudo C s j =>
    let bp := baseProd op
    let bI : TA V α := single B r
    let bV : TA V α := topSingle i
    let cI : TA V α := single C s
    let cV : TA V α := topSingle j
    match op with
    | .mul =>
      if B == C then
        let out := baseProd .mul bI cV + baseProd .mul bV cI
        coupleOf (r * s * Coeff.ofRat (scalarCoef V .mul B B) +
          i * j * Coeff.ofRat (scalarCoef V .mul (pseudoBits V) (pseudoBits V))) out
      else bp bV cV + bp bI cI + bp bI cV + bp bV cI
    | .wedge =>
      if B == C then (if B == 0 then pseudo B (r * s) (r * j + i * s) else zero) else bp bI cI
    | .vee => if B == C then pseudo B (r * j + i * s) (i * j) else tc a cI + tc a cV
    | .contraction =>
      if B == C then
        coupleOf (r * s * Coeff.ofRat (scalarCoef V .contraction B B) +
          i * j * Coeff.ofRat (scalarCoef V .contraction (pseudoBits V) (pseudoBits V)))
          (baseProd .contraction bV cI)
      else tc bI b + tc bV b
  | couple _ r i, pseudo C s j =>
    let B := match a with | couple B .. => B | _ => 0
    match op with
    | .mul => tc (single 0 r) b + tc (single B i) b
    | .wedge => tc (single 0 r) b + baseProd .wedge (single B i) (single C s)
    | .vee => baseProd .vee (single 0 r) (topSingle j) + tc (single B i) b
    | .contraction => baseProd .contraction (single 0 r) (single C s) + tc (single B i) b
  | pseudo B r i, couple C s j =>
    match op with
    | .mul => tc a (single 0 s) + tc a (single C j)
    | .wedge => tc a (single 0 s) + baseProd .wedge (single B r) (single C j)
    | .vee => baseProd .vee (topSingle i) (single 0 s) + tc a (single C j)
    | .contraction => tc a (single 0 s) + tc a (single C j)
  | _, _ => tc a b

/-! ## Julia's products -/

/-- Julia `a * b`, `a ⟑ b` (the geometric product). -/
@[inline] def mul (a b : TA V α) : TA V α := prod .mul a b
/-- Julia `a ∧ b`. -/
@[inline] def wedge (a b : TA V α) : TA V α := prod .wedge a b
/-- Julia `a ∨ b`. -/
@[inline] def vee (a b : TA V α) : TA V α := prod .vee a b
/-- Julia `contraction(a, b)` (`a ⋅ b`, `a ⨽ b`, the right contraction). -/
@[inline] def contraction (a b : TA V α) : TA V α := prod .contraction a b
/-- Julia `a ⨼ b = contraction(b, a)` (AbstractTensors `src/AbstractTensors.jl:259`). -/
@[inline] def lcontraction (a b : TA V α) : TA V α := contraction b a
/-- Julia `a << b = contraction(b, ~a)` (`src/AbstractTensors.jl:260`). -/
@[inline] def lshift (a b : TA V α) : TA V α := contraction b (reverse a)
/-- Julia `a >> b = contraction(~a, b)` (`src/AbstractTensors.jl:261`). -/
@[inline] def rshift (a b : TA V α) : TA V α := contraction (reverse a) b
/-- Julia `a ∗ b = (~a) ⟑ b`, the reverse product (`src/AbstractTensors.jl:257`). -/
@[inline] def revmul (a b : TA V α) : TA V α := mul (reverse a) b
/-- Julia `a ⊛ b = scalar(contraction(a, b))` (`src/AbstractTensors.jl:258`). -/
@[inline] def scalarprod (a b : TA V α) : TA V α := scalar (contraction a b)
/-- Julia `a × b = ⋆(a ∧ b)` (`src/AbstractTensors.jl:349`). -/
@[inline] def cross (a b : TA V α) : TA V α := hodge (wedge a b)
/-- Julia `veedot(a, b) = complementleft(!a ⟑ !b)` (`a ⟇ b`, `src/algebra.jl:391`). -/
@[inline] def veedot (a b : TA V α) : TA V α :=
  complementleft (mul (complementright a) (complementright b))
/-- Julia `antidot(a, b) = complementleft(contraction(!a, !b))` (`src/algebra.jl:396`). -/
@[inline] def antidot (a b : TA V α) : TA V α :=
  complementleft (contraction (complementright a) (complementright b))

instance : Mul (TA V α) := ⟨mul⟩

/-! ## Sandwich products (`src/algebra.jl:313-385, 1560-1790`) -/

/-- Whether Julia's generated `product_sandwich` takes the versor `y` (a graded element,
a half, a `Couple` on an even blade, a `PseudoCouple` whose blade has the parity of
`n`); otherwise the versor is a `Multivector` (or made one by `multispin`). -/
def versorGraded : TA V α → Bool
  | multi _ | infinity | phasor .. => false
  | couple b .. => popcount b % 2 == 0
  | pseudo b .. => popcount b % 2 == V.n % 2
  | _ => true

/-- Whether an element is a term (`Zero`, `One`, a blade, a `Single`). -/
def isTerm : TA V α → Bool
  | zero | one | blade _ | single .. => true
  | _ => false

/-- Whether an element is graded (a term or a chain). -/
def isGraded (x : TA V α) : Bool := isTerm x || (match x with | chain .. => true | _ => false)

/-- Whether `parityclifford(k)`: Julia's `clifford` negates grade `k`. -/
@[inline] def cliffordNeg (k : Nat) : Bool := (k * (k + 1) / 2) % 2 == 1

/-- The versor `y` of a generated sandwich as a loop operand, with the parity of its
grades; the entries are `yc`'s (`y` or `clifford(y)`: Julia's `par ? -b.v[i] : b.v[i]`,
computed by the caller, in Julia in the versor's own coefficient type). A
`Couple`/`PseudoCouple` is its `B` term followed by its scalar/volume term. -/
def versorSrc? (y yc : TA V α) : Option (Loops.JSrc × Packed.Arr α × Nat) :=
  let parts := fun (b : UInt64) (top : Bool) (re im : α) =>
    let c := if top then pseudoBits V else 0
    match yc with
    | couple b' r i => if b' == b && !top then (i, r) else (yc.coeff b, yc.coeff c)
    | pseudo b' r i => if b' == b && top then (r, i) else (yc.coeff b, yc.coeff c)
    | _ => if top then (re, im) else (im, re)
  let dense := fun (p : Nat) =>
    match loopSrc? yc, loopSrc? y with
    | some (s, x), some (s', _) => if s == s' then some (s, x, p) else none
    | _, _ => none
  match y with
  | one => some (.terms #[0], Loops.termArr (yc.coeff 0), 0)
  | blade b => some (.terms #[b], Loops.termArr (yc.coeff b), popcount b % 2)
  | single b _ => some (.terms #[b], Loops.termArr (yc.coeff b), popcount b % 2)
  | couple b re im =>
    let (u, w) := parts b false re im
    some (.terms #[b, 0], Loops.termArr₂ u w, popcount b % 2)
  | pseudo b re im =>
    let (u, w) := parts b true re im
    some (.terms #[b, pseudoBits V], Loops.termArr₂ u w, popcount b % 2)
  | chain g _ => dense (g % 2)
  | spinor _ => dense 0
  | cospinor _ => dense 1
  | _ => none

/-- Julia's generated `product_sandwich` of a graded `x` of grade `G` by the versor `y`,
both passes by Julia's loops, projected onto grade `G` (`Chain{V,G}`): the first pass with
the versor entries `y₁`, the second with `y₂` (`clifford(y)`, `y` for `⊘`; `y`,
`clifford(y)` for `>>>`). -/
def sandwichLoop (G : Nat) (x y y₁ y₂ : TA V α) : TA V α :=
  match versorSrc? y y₁, loopSrc? x, versorSrc? y y₂ with
  | some (sy, a₁, p), some (sx, xa), some (_, a₂, _) =>
    let k : Loops.SKey := { V, y := sy, x := sx, mid := halfL ((p + G) % 2 == 1), G }
    chain G ⟨Loops.runS k a₁ xa a₂⟩
  | _, _, _ => zero

/-- `x ⊘ y` with the versor's images supplied (`yr = ~y`, `yi = involute(y)`,
`yc = clifford(y)`; Julia computes them in the versor's own coefficient type, before any
promotion against `x`): see `sandwich`. -/
def sandwichWith (x y yr yi yc : TA V α) : TA V α :=
  let generic := fun (x yr yi : TA V α) => mul (mul yr x) yi
  let one := fun (x : TA V α) =>
    if isTerm x && isTerm y then generic x yr yi
    else if isGraded x && versorGraded y then
      match x.grade? with
      | some G => sandwichLoop G x y yc y
      | none => generic x yr yi
    else if isGraded x then generic x (multispin yr) (multispin yi)
    else generic x yr yi
  match x with
  | couple B r i => one (single 0 r) + one (single B i)
  | pseudo B r i => one (single B r) + one (topSingle i)
  | _ => one x

/-- Julia `x ⊘ y = (~y) ⟑ x ⟑ involute(y)`; when Julia's generated method applies (a
graded `x`, see `versorGraded`) it is the two-pass loop `clifford(y) ⟑ x ⟑ y` (the same
value) projected onto the grade of `x`; a `Couple`/`PseudoCouple` `x` is sandwiched part
by part. -/
@[inline] def sandwich (x y : TA V α) : TA V α :=
  sandwichWith x y (reverse y) (involute y) (clifford y)

/-- `y >>> x` with `yc = clifford(y)` supplied (see `sandwichWith`). -/
def tsandwichWith (y yc x : TA V α) : TA V α :=
  let generic := fun (y yc x : TA V α) => mul (mul y x) yc
  let one := fun (x : TA V α) =>
    if isTerm x && isTerm y then generic y yc x
    else if isGraded x && versorGraded y then
      match x.grade? with
      | some G => sandwichLoop G x y y yc
      | none => generic y yc x
    else if isGraded x then generic (multispin y) (multispin yc) x
    else generic y yc x
  match x with
  | couple B r i => one (single 0 r) + one (single B i)
  | pseudo B r i => one (single B r) + one (topSingle i)
  | _ => one x

/-- Julia `y >>> x = y ⟑ x ⟑ clifford(y)` (the versor on the left), projected like
`sandwich`. Julia's generated fallback for a versor that is not parity-homogeneous swaps
the operands (defect `tsandwich-mixed-parity-swap`); here it is `multispin(y) >>> x`. -/
@[inline] def tsandwich (y x : TA V α) : TA V α := tsandwichWith y (clifford y) x

end TA

end Grassmann
