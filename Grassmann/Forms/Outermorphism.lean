/-
`Outermorphism`: the extension of a grade-1 map to the whole exterior algebra
(Julia `Outermorphism{V,T<:Tuple}`, Grassmann.jl `src/forms.jl:712-800,
1043-1073`; port-notes/grassmann-forms.md §2.8, §4.4-4.5).

Julia stores the tuple of compound matrices `(Λ¹F, …, Λᵏ F)`, `k = min(n, m)`
(the grade-0 block is the implicit `1`); `F(v₁∧…∧v_g) = F(v₁)∧…∧F(v_g)`. Here
the blocks are an array of runtime-shaped matrices (`Forms.DMat`), block `g-1`
being the `C(m,g) × C(n,g)` compound `Λᵍ F`; `block g` reads it back with its
static type (a runtime shape check that always succeeds for values built here).

As in Julia, `+`, `-` and scalar multiplication act blockwise (`2O` scales every
compound by `2`, not `2ᵍ`, and leaves the grade-0 block at `1`), so they break
the compound invariant exactly as Julia does; the other operations
(`inv`, `adjugate`, composition, ...) recompute every compound from the grade-1
block, as Julia does.

Fixed Julia defects (port-notes §8.4): `transpose` (a `MethodError` in Julia,
item 5) and the zero padding of `O ⋅ Spinor`/`O ⋅ CoSpinor` when `min(n, m)` is
odd (item 6: Julia pads with grades of the wrong parity).
-/
import Grassmann.Forms.Compound

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

namespace Forms

/-- A matrix with a runtime shape. -/
structure DMat (α : Type) [Coeff α] where
  /-- Number of rows. -/
  rows : Nat
  /-- Number of columns. -/
  cols : Nat
  /-- The entries. -/
  mat : Mat rows cols α

namespace DMat

variable {α : Type} [Coeff α]

/-- Forget the static shape. -/
@[inline] def ofMat {r c : Nat} (A : Mat r c α) : DMat α := ⟨r, c, A⟩

/-- Read back at a static shape (zero if the shape differs). -/
@[inline] def toMat (A : DMat α) (r c : Nat) : Mat r c α :=
  if h : A.rows = r ∧ A.cols = c then A.mat.cast h.1 h.2 else Mat.zero

/-- Entrywise combination of two matrices of the same shape (the first operand's
shape wins otherwise). -/
@[inline] def zipWith (f : α → α → α) (A B : DMat α) : DMat α :=
  ⟨A.rows, A.cols, A.mat.zipWith f (B.toMat A.rows A.cols)⟩

/-- Map the entries. -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (A : DMat α) : DMat β := ⟨A.rows, A.cols, A.mat.map f⟩

instance [BEq α] : BEq (DMat α) := ⟨fun A B => A.rows == B.rows && A.cols == B.cols &&
  A.mat.v.toArray == B.mat.v.toArray⟩

end DMat

/-- The grades a layout stores, in storage order (`full`: `0 … n`, `even`: the
even ones, `odd`: the odd ones, `chain g`: `g` alone if `g ≤ n`). -/
def layoutGrades (n : Nat) : Layout → List Nat
  | .chain g => if g ≤ n then [g] else []
  | .even => (List.range (n + 1)).filter (· % 2 == 0)
  | .odd => (List.range (n + 1)).filter (· % 2 == 1)
  | .full => List.range (n + 1)

/-- The grade-`g` block of a coefficient vector stored in layout `l` (the grades
of a layout are stored grade-major, lexicographic within a grade). -/
@[specialize] def gradeBlock {α : Type} [Coeff α] (n : Nat) (l : Layout) (x : Values α (l.size n)) (g : Nat) :
    Values α (Leibniz.binomial n g) :=
  let off := ((layoutGrades n l).takeWhile (· != g)).foldl (fun acc k => acc + Leibniz.choose n k) 0
  Values.ofFn fun i => getD x (off + i.1)

/-- Concatenate per-grade blocks into layout `l` (grades in storage order). -/
@[specialize] def ofGradeBlocks {α : Type} [Coeff α] (n : Nat) (l : Layout) (f : (g : Nat) → Values α (Leibniz.binomial n g)) :
    Values α (l.size n) :=
  let arr := (layoutGrades n l).foldl (fun (acc : Array α) g => acc ++ (f g).toArray) #[]
  Values.ofFn fun i => arr[i.1]?.getD Coeff.zero

end Forms

/-- Julia `Outermorphism{V}`: the compound matrices `Λ¹F … Λᵏ F`,
`k = min(n, m)`, of a map `F : V → W` (`forms.jl:714-721`). -/
structure Outermorphism (V W : TensorBundle) (α : Type) [Coeff α] where
  /-- Block `g - 1` is the `C(m,g) × C(n,g)` compound `Λᵍ F`. -/
  blocks : Array (DMat α)

namespace Outermorphism

variable {V W U : TensorBundle} {α : Type} [Coeff α]

/-- `k = min(n, m)`: the number of stored compounds. -/
@[inline] def depth (_ : Outermorphism V W α) : Nat := min V.n W.n

/-- The `g`-th compound (Julia `O[g]`, `compound(O, g)`, `forms.jl:740, 762`);
the `1 × 1` identity for `g = 0` and zero beyond `min(n, m)`. -/
@[specialize] def block (O : Outermorphism V W α) (g : Nat) : TensorOperator V (.chain g) W (.chain g) α :=
  if g = 0 then TensorOperator.identity
  else match O.blocks[g - 1]? with
    | some b => ⟨b.toMat _ _⟩
    | none => TensorOperator.zero

/-- Julia `outermorphism(F)` of a grade-1 map (`forms.jl:719-721`): its compounds. -/
@[specialize] def ofSimplex (F : Simplex V W α) : Outermorphism V W α :=
  ⟨((List.range (min V.n W.n)).map fun k => DMat.ofMat (F.compound (k + 1)).mat).toArray⟩

/-- The grade-1 map (Julia `O.v[1]`). -/
@[inline] def base (O : Outermorphism V W α) : Simplex V W α := O.block 1

/-- Whether layout `l` stores grade `g` (`Forms.layoutGrades` as a predicate). -/
@[inline] def storesGrade (g : Nat) : Layout → Bool
  | .chain h => g == h
  | .even => g % 2 == 0
  | .odd => g % 2 == 1
  | .full => true

/-- Push `rg` zeros. -/
@[specialize] def pushZeros (rg : Nat) (out : Packed.Arr α) : Packed.Arr α :=
  Mat.pushLoop (fun _ => Coeff.zero) rg 0 out

/-- The grades `g, …, m` of `applyValues`: the codomain grades stored in `l`, the domain block
of grade `g` at `off` (the sizes of the domain's lower stored grades). -/
@[specialize] def applyLoop (O : Outermorphism V W α) (l : Layout) (xd : Packed.Arr α) (k n m : Nat) :
    (g off : Nat) → Packed.Arr α → (fuel : Nat) → Packed.Arr α
  | _, _, out, 0 => out
  | g, off, out, fuel + 1 =>
    if g > m then out
    else if !storesGrade g l then applyLoop O l xd k n m (g + 1) off out fuel
    else
      let inDom := g ≤ n
      let off' := if inDom then off + Leibniz.choose n g else off
      let rg := Leibniz.choose m g
      let out :=
        if g = 0 then Packed.push out (Mat.rd xd off)
        else if g ≤ k && inDom then
          -- a bounds-checked index, not `blocks[g - 1]?` (an `Option` allocated per grade)
          if h : g - 1 < O.blocks.size then
            let b := O.blocks[g - 1]
            let a := b.mat.v.data
            Mat.pushLoop (fun i => Mat.sdot0 id a xd b.rows 1 b.cols i off) rg 0 out
          else pushZeros rg out
        else pushZeros rg out
      applyLoop O l xd k n m (g + 1) off' out fuel

/-- Whether block `g - 1` of `O` is square of side `d` (its storage read at run time). -/
@[inline] def blockSide (O : Outermorphism V W α) (g d : Nat) : Bool :=
  if h : g - 1 < O.blocks.size then
    let b := O.blocks[g - 1]
    b.rows == d && b.cols == d
  else false

/-- The generated straight-line `applyValues .full` (`Grassmann.Forms.Unrolled.applyFull3…4`,
bit-identical to `applyLoop`) for the compounds of an endomorphism of `n = 3, 4` generators
(what `ofSimplex` builds: `C(n, g) × C(n, g)` blocks), else `fallback`. -/
@[specialize] def applyFullOr (O : Outermorphism V W α) (xd : Packed.Arr α) (fallback : Unit → Packed.Arr α) :
    Packed.Arr α :=
  let bl := fun (g : Nat) => if h : g - 1 < O.blocks.size then O.blocks[g - 1].mat.v.data else xd
  if V.n == 3 && W.n == 3 && O.blocks.size == 3 && O.blockSide 1 3 && O.blockSide 2 3 && O.blockSide 3 1 then
    Unrolled.applyFull3 (bl 1) (bl 2) (bl 3) xd
  else if V.n == 4 && W.n == 4 && O.blocks.size == 4 && O.blockSide 1 4 && O.blockSide 2 6 &&
      O.blockSide 3 4 && O.blockSide 4 1 then
    Unrolled.applyFull4 (bl 1) (bl 2) (bl 3) (bl 4) xd
  else fallback ()

/-- The image of a coefficient vector stored in layout `l` (Julia `contraction(O, x)`,
`forms.jl:1050-1073`): the scalar part is kept, grade `g ≤ k` goes through
`Λᵍ F`, higher grades of the codomain are zero. One tail-recursive pass over the grades,
no intermediate lists; the result size is checked with `Forms.layoutSize` (no `Nat` powers).
The algorithm `Grassmann.Forms.Unrolled.applyFull3…4` are generated from. -/
@[specialize] def applyValuesGeneric (O : Outermorphism V W α) (l : Layout) (x : Values α (l.size V.n)) :
    Values α (l.size W.n) :=
  let m := W.n
  let res := applyLoop O l x.data O.depth V.n m 0 0 (Packed.mkEmpty (layoutSize m l)) (m + 1)
  if h : Packed.size res = layoutSize m l then ⟨res, h.trans (layoutSize_eq m l)⟩
  else zeroValues _

/-- `applyValuesGeneric`, with the generated straight-line forms for full coefficient vectors
of `n = 3, 4` generators (`applyFullOr`, bit-identical). -/
@[specialize] def applyValues (O : Outermorphism V W α) (l : Layout) (x : Values α (l.size V.n)) :
    Values α (l.size W.n) :=
  let m := W.n
  let loop := fun (_ : Unit) => applyLoop O l x.data O.depth V.n m 0 0 (Packed.mkEmpty (layoutSize m l)) (m + 1)
  let res := match l with
    | .full => applyFullOr O x.data loop
    | _ => loop ()
  if h : Packed.size res = layoutSize m l then ⟨res, h.trans (layoutSize_eq m l)⟩
  else zeroValues _

/-- Julia `O(x) = O ⋅ x` for any element of the domain algebra (`forms.jl:723,
1050-1073`): a `Chain` of grade `g` goes to a `Chain` of grade `g`, a `Spinor`
to a `Spinor`, a `CoSpinor` to a `CoSpinor`, a `Multivector` to a `Multivector`. -/
@[inline] def apply {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout W l α Y]
    (O : Outermorphism V W α) (x : X) : Y :=
  OfLayout.ofVals (V := W) (l := l) (O.applyValues l (InLayout.vals x))

/-- Julia `O ⋅ Couple` (`forms.jl:1054`): the sum of the images of its parts,
a `Multivector` of the codomain. -/
@[specialize] def applyCouple (O : Outermorphism V W α) (z : Couple V α) : Multivector W α :=
  ⟨O.applyValues .full (toMultivector z).v⟩

/-- Julia `O ⋅ PseudoCouple` (`forms.jl:1055`). -/
@[specialize] def applyPseudoCouple (O : Outermorphism V W α) (z : PseudoCouple V α) : Multivector W α :=
  ⟨O.applyValues .full (toMultivector z).v⟩

/-- The full `2ᵐ × 2ⁿ` block-diagonal matrix (Julia `TensorOperator(O)`,
`forms.jl:765-774`): `1` at the scalar, then every compound on its grade. -/
@[specialize] def toOperator (O : Outermorphism V W α) : TensorOperator V .full W .full α :=
  TensorOperator.ofFn fun i j =>
    let bi := (Leibniz.indexBasisAll W.n)[i.1]!
    let bj := (Leibniz.indexBasisAll V.n)[j.1]!
    let gi := DirectSum.Bits.popcount bi
    let gj := DirectSum.Bits.popcount bj
    if gi != gj then Coeff.zero
    else if gi = 0 then Coeff.one
    else (O.block gi).entry (Leibniz.bladeRank W.n bi) (Leibniz.bladeRank V.n bj)

/-- Julia `tr(O) = 1 + Σ_g tr(Λᵍ F)` (`forms.jl:744`); for a square `F` this
is `det(I + F)`. -/
@[specialize] def tr (O : Outermorphism V W α) : α :=
  (List.range O.blocks.size).foldl (fun acc k => acc + (O.block (k + 1)).tr) Coeff.one

/-- Julia `scalar(O) = tr(O) / 2ⁿ` (`forms.jl:743`). -/
@[inline] def scalar [Div α] (O : Outermorphism V W α) : α := O.tr / Coeff.ofInt (pow2 V.n)

/-- Julia `∧(O)` (`forms.jl:746-753`): the first column of the top compound
`Λᵏ F`, `k = min(n, m)`; for a square map the pseudoscalar `det(F)·I` of the
codomain. (For `n > m` Julia instead collects the `C(n,m)` scalars of the
`1 × C(n,m)` top compound.) -/
@[specialize] def wedgeAll (O : Outermorphism V W α) : Chain W (min V.n W.n) α :=
  let B := O.block (min V.n W.n)
  ⟨Values.ofFn fun i => B.entry i.1 0⟩

/-- Julia `det(O) = !∧(O)` (`forms.jl:745`): `det(F)` for a square map. -/
@[inline] def det (O : Outermorphism V W α) : α := Forms.at0 O.wedgeAll.v

/-- The compounds with a function applied to each (Julia `Outermorphism{V}(map(f, value(O)))`). -/
@[inline] def mapBlocks {β : Type} [Coeff β] (f : DMat α → DMat β) (O : Outermorphism V W α) :
    Outermorphism V W β := ⟨O.blocks.map f⟩

/-- Map every entry of every compound (Julia `map(f, O)` on the blocks). -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (O : Outermorphism V W α) : Outermorphism V W β :=
  O.mapBlocks (DMat.map f)

/-- The transpose `W → V` blockwise (Julia `transpose(O)`, `forms.jl:742`, a
`MethodError` there). -/
@[specialize] def transpose (O : Outermorphism V W α) : Outermorphism W V α :=
  ⟨O.blocks.map fun b => DMat.ofMat b.mat.transpose⟩

/-- The zero outermorphism (Julia `zero(O)`: zero compounds, `forms.jl:757-760`). -/
def zero (O : Outermorphism V W α) : Outermorphism V W α := O.mapBlocks fun b => ⟨b.rows, b.cols, Mat.zero⟩

instance : Add (Outermorphism V W α) := ⟨fun a b => ⟨Array.zipWith (DMat.zipWith (· + ·)) a.blocks b.blocks⟩⟩
instance : Sub (Outermorphism V W α) := ⟨fun a b => ⟨Array.zipWith (DMat.zipWith (· - ·)) a.blocks b.blocks⟩⟩
instance : Neg (Outermorphism V W α) := ⟨fun a => a.map (- ·)⟩
/-- Julia `a * O` scales every compound by `a` (`forms.jl:1110-1115`). -/
instance : HMul α (Outermorphism V W α) (Outermorphism V W α) := ⟨fun s O => O.map (s * ·)⟩
instance : HMul (Outermorphism V W α) α (Outermorphism V W α) := ⟨fun O s => O.map (· * s)⟩
/-- Julia `O / s`: every compound times `1/s` (`forms.jl:1112`, through the reciprocal). -/
instance [Div α] : HDiv (Outermorphism V W α) α (Outermorphism V W α) :=
  ⟨fun O s => let r := Coeff.one / s; O.map (· * r)⟩
/-- Julia `a == b` (master `forms.jl:755`). -/
instance [BEq α] : BEq (Outermorphism V W α) := ⟨fun a b => a.blocks == b.blocks⟩
instance : Inhabited (Outermorphism V W α) := ⟨⟨#[]⟩⟩

/-- Julia `O ⋅ O'` (`forms.jl:1052`): compose the grade-1 maps and recompute the
compounds. -/
@[inline] def comp (A : Outermorphism W U α) (B : Outermorphism V W α) : Outermorphism V U α :=
  ofSimplex (A.base.comp B.base)

/-- Julia `inv(O)`, recomputed from `inv(F)` (`forms.jl:780-782`). -/
@[inline] def inv [Div α] (O : Outermorphism V W α) : Outermorphism W V α := ofSimplex O.base.inv

/-- Julia `adjugate(O)` (`forms.jl:780-782`). -/
@[inline] def adjugate (O : Outermorphism V W α) : Outermorphism W V α := ofSimplex O.base.adjugate

/-- Julia `cofactor(O)` (`forms.jl:780-782`). -/
@[inline] def cofactor (O : Outermorphism V W α) : Outermorphism V W α := ofSimplex O.base.cofactor

/-- Julia `invdet(O) = (Outermorphism(inv F), det F)` (`forms.jl:776-779`). -/
@[inline] def invdet [Div α] (O : Outermorphism V W α) : Outermorphism W V α × α :=
  (O.inv, O.base.det)

/-- Julia `O ⋅ T` for an endomorphism of grade `g`: `Λᵍ F ∘ T` (`forms.jl:1043`). -/
@[inline] def compOperator {g : Nat} (O : Outermorphism W U α) (T : TensorOperator V (.chain g) W (.chain g) α) :
    TensorOperator V (.chain g) U (.chain g) α :=
  (O.block g).comp T

/-- Julia `T ⋅ O` for an operator of grade `g`: `T ∘ Λᵍ F` (`forms.jl:1044`). -/
@[inline] def operatorComp {g : Nat} (T : TensorOperator W (.chain g) U (.chain g) α)
    (O : Outermorphism V W α) : TensorOperator V (.chain g) U (.chain g) α :=
  T.comp (O.block g)

instance {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout W l α Y] :
    HMul (Outermorphism V W α) X Y := ⟨apply⟩
instance {l : Layout} {X Y : Type} [InLayout X V l α] [OfLayout W l α Y] :
    Contraction (Outermorphism V W α) X Y := ⟨apply⟩
instance : HMul (Outermorphism W U α) (Outermorphism V W α) (Outermorphism V U α) := ⟨comp⟩
instance : Contraction (Outermorphism W U α) (Outermorphism V W α) (Outermorphism V U α) := ⟨comp⟩

end Outermorphism

namespace TensorOperator

variable {V W : TensorBundle} {α : Type} [Coeff α]

/-- Julia `outermorphism(T)` / `Outermorphism(T)` of a grade-1 operator. -/
@[inline] def outermorphism (T : Simplex V W α) : Outermorphism V W α := Outermorphism.ofSimplex T

end TensorOperator

end Grassmann
