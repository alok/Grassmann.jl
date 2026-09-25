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

/-! ## Layouts of the dense kinds -/

/-- The storage layout and entries of a term or container (`none` for couples,
`Zero`, `∞`, phasors). A term is a one-hot chain. -/
def layoutValues? (x : TA V α) : Option ((l : Layout) × Values α (l.size V.n)) :=
  match x with
  | one => some ⟨.chain 0, (chainOf V 0 fun β => if β == 0 then Coeff.one else Coeff.zero).v⟩
  | blade b => some ⟨.chain (popcount b), (chainOf V (popcount b) fun β => if β == b then Coeff.one else Coeff.zero).v⟩
  | single b v => some ⟨.chain (popcount b), (chainOf V (popcount b) fun β => if β == b then v else Coeff.zero).v⟩
  | chain g c => some ⟨.chain g, c.v⟩
  | spinor h => some ⟨.even, h.v⟩
  | cospinor h => some ⟨.odd, h.v⟩
  | multi m => some ⟨.full, m.v⟩
  | _ => none

/-- A container of layout `l`. -/
def ofLayout (l : Layout) (v : Values α (l.size V.n)) : TA V α :=
  match l, v with
  | .chain g, v => chain g ⟨v⟩
  | .even, v => spinor ⟨v⟩
  | .odd, v => cospinor ⟨v⟩
  | .full, v => multi ⟨v⟩

/-- The product `op(a, b)` of two dense elements evaluated by the space's kernels into
layout `lc` (contributions outside `lc` are dropped: callers choose Julia's layout, which
holds them all). -/
def kernelInto (op : POp) (lc : Layout) (a b : TA V α) : TA V α :=
  match layoutValues? a, layoutValues? b with
  | some ⟨la, x⟩, some ⟨lb, y⟩ => ofLayout lc (Kernels.binProj op.bin la lb lc x y)
  | _, _ => zero

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
case `a` is a term. -/
def gradedChain (op : POp) (a : TA V α) (L : Nat) {G : Nat} (c : Chain V G α) (swap : Bool) : TA V α :=
  let b : TA V α := chain G c
  let n := V.n
  let tangent := V.istangent
  let isChain := match a with | chain .. => true | _ => false
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
    else if swap then kernelInto op (halfL ((L + G) % 2 == 1)) b a
    else kernelInto op (halfL ((L + G) % 2 == 1)) a b
  | .wedge =>
    if L + G > n && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent then (if swap then kernelInto op .full b a else kernelInto op .full a b)
    else if swap then kernelInto op (.chain (L + G)) b a else kernelInto op (.chain (L + G)) a b
  | .vee =>
    if L + G < n && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent then (if swap then kernelInto op .full b a else kernelInto op .full a b)
    else if swap then kernelInto op (.chain (L + G - n)) b a else kernelInto op (.chain (L + G - n)) a b
  | .contraction =>
    if (if swap then G < L else L < G) && !tangent then zero
    else if (G == 0 || G == n) && !tangent then withSingle sb
    else if tangent || V.hasconformal then
      (if swap then kernelInto op .full b a else kernelInto op .full a b)
    else if swap then kernelInto op (.chain (G - L)) b a else kernelInto op (.chain (L - G)) a b

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

/-- Julia's `maxgrade`, `mingrade`, `nextgrade`, `maxpseudograde` of a container
(`src/multivectors.jl:1156-1197`): `(min, max, next, maxpseudo)`. -/
def gradeRange (V : TensorBundle) : TA V α → Nat × Nat × Nat × Nat
  | spinor _ => (0, if V.n % 2 == 1 then V.n - 1 else V.n, 2, V.n)
  | cospinor _ => (1, if V.n % 2 == 1 then V.n else V.n - 1, 2, V.n - 1)
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
grade blocks of `b`). -/
def gradedContainer (core : POp → TA V α → TA V α → TA V α) (op : POp) (a : TA V α) (G : Nat)
    (b : TA V α) (swap : Bool) : TA V α :=
  let n := V.n
  let tangent := V.istangent
  let (mn, mx, nx, mxp) := gradeRange V b
  let blk := fun (g : Nat) => gradeProj g b
  let app := fun (x : TA V α) => if swap then core op x a else core op a x
  let generic := fun (_ : Unit) =>
    if swap then kernelInto op (containerOut op G b) b a else kernelInto op (containerOut op G b) a b
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
    if G + mn > n && !tangent then zero
    else if G + mn == n && !tangent then app (blk mn)
    else if G + (mn + nx) == n && !tangent then app (blk mn) + app (blk (mn + nx))
    else generic ()
  | .vee =>
    if G + mx < n && !tangent then zero
    else if G + mx == n && !tangent then app (blk mx)
    else if G + (mx - nx) == n && !tangent then app (blk mx) + app (blk (mx - nx))
    else generic ()
  | .contraction =>
    if (if swap then mx < G else G < mn) && !tangent then zero
    else if (if swap then mx == G else G + mxp == n) && !tangent then
      (if swap then core op (blk mx) a else core op a (blk mn))
    else if (if swap then mx - nx == G else G + (mxp - nx) == n) && !tangent then
      (if swap then core op (blk mx) a + core op (blk (mx - nx)) a
       else core op a (blk mn) + core op a (blk (mn + nx)))
    else generic ()

/-- The product of two containers (halves and multivectors; `src/products.jl:1146-1320`). -/
def containerContainer (op : POp) (a b : TA V α) : TA V α :=
  let parity := fun (x : TA V α) => match x with
    | spinor _ => some false
    | cospinor _ => some true
    | _ => none
  match parity a, parity b with
  | some p, some q =>
    let r := p ^^ q
    let r := if op == .vee then r ^^ (V.n % 2 == 1) else r
    kernelInto op (halfL r) a b
  | _, _ => kernelInto op .full a b

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

/-- The grade-`G` part of the dense sandwich `y₁ ⟑ x ⟑ y₂` (Julia's generated
`product_sandwich` returns `Chain{V,G}` of it): two kernel products, the second
projected onto grade `G`. -/
def sandwichProj (G : Nat) (y₁ x y₂ : TA V α) : TA V α :=
  let d := fun (t : TA V α) => (t.toDense).v
  let t : Values α (Layout.full.size V.n) := Kernels.bin .mul .full .full .full (d y₁) (d x)
  chain G ⟨Kernels.binProj .mul .full .full (.chain G) t (d y₂)⟩

/-- Julia `x ⊘ y = (~y) ⟑ x ⟑ involute(y)`, projected onto the grade of a graded `x`
when Julia's generated method applies (see `versorGraded`); a `Couple`/`PseudoCouple`
`x` is sandwiched part by part. -/
def sandwich (x y : TA V α) : TA V α :=
  let generic := fun (x y : TA V α) => mul (mul (reverse y) x) (involute y)
  let one := fun (x : TA V α) =>
    if isTerm x && isTerm y then generic x y
    else if isGraded x && versorGraded y then
      match x.grade? with
      | some G => sandwichProj G (reverse y) x (involute y)
      | none => generic x y
    else if isGraded x then generic x (multispin y)
    else generic x y
  match x with
  | couple B r i => one (single 0 r) + one (single B i)
  | pseudo B r i => one (single B r) + one (topSingle i)
  | _ => one x

/-- Julia `y >>> x = y ⟑ x ⟑ clifford(y)` (the versor on the left), projected like
`sandwich`. Julia's generated fallback for a versor that is not parity-homogeneous swaps
the operands (defect `tsandwich-mixed-parity-swap`); here it is `multispin(y) >>> x`. -/
def tsandwich (y x : TA V α) : TA V α :=
  let generic := fun (y x : TA V α) => mul (mul y x) (clifford y)
  let one := fun (x : TA V α) =>
    if isTerm x && isTerm y then generic y x
    else if isGraded x && versorGraded y then
      match x.grade? with
      | some G => sandwichProj G y x (clifford y)
      | none => generic y x
    else if isGraded x then generic (multispin y) x
    else generic y x
  match x with
  | couple B r i => one (single 0 r) + one (single B i)
  | pseudo B r i => one (single B r) + one (topSingle i)
  | _ => one x

end TA

end Grassmann
