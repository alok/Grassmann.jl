/-
Julia display of operators (Grassmann.jl `src/forms.jl:365-372, 427-464, 543-553,
660-710, 790-800, 1731-1764`, `src/multivectors.jl:46-58, 109-116, 340-356, 589-615`;
port-notes/grassmann-forms.md §5).

* **2-arg `show`** (`toString`): the nested chain, `(1v₁+2v₂+3v₃)v₁ + (4v₁+5v₂+6v₃)v₂ + …`.
  The outer element prints with Julia's per-type rule (every term for `Chain`
  and `CoSpinor`; the first coefficient raw then every term for `Spinor`; the
  first coefficient raw then the nonzero terms for `Multivector`, `1v⃖ + (0+1v₁)v₁ + …`),
  its coefficients (the columns) in parentheses and in a compact context, so
  that the inner elements print without spaces and with 6 significant digits.
  Diagonal operators and outermorphisms print as their materialised operator.
* **3-arg `show`** (`display`): Julia's `summary` line and `print_matrix` of
  `display_matrix(T)`: a header row with the domain pseudoscalar and the domain
  blades, a first column of codomain blades, aligned exactly as Julia's
  `Base.print_matrix` does (`alignment`: integers and blades right-aligned, reals
  aligned on the decimal point, complex numbers on the sign of the imaginary part;
  widths are `textwidth`, where the combining `⃖` counts zero). The summary uses
  Julia's type names for grade-1 and grade-`g` operators over `Int`, `Float` and
  complex floats; tests compare the matrix body byte for byte.
* `Projector`, `SpectralOperator`, `Dyadic` (`forms.jl:427-428, 464`), and TeX
  (`printtex`, `alltex`, `forms.jl:1731-1764`) for operators and Cayley tables.
-/
import Grassmann.Forms.Cayley
import Grassmann.Types.Show

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms JuliaBase

namespace Forms.Show

variable {α : Type} [Coeff α] [JuliaShow α]

/-- Julia's `textwidth`: the number of characters, combining marks (`⃖`, U+20D6)
counting zero. -/
def textwidth (s : String) : Nat := s.foldl (fun n c => if c.toNat == 0x20D6 then n else n + 1) 0

/-- The coefficients of layout `l` of `W` with their blades, in storage order. -/
def terms {n : Nat} (W : TensorBundle) (l : Layout) (x : Values α n) : List (UInt64 × α) :=
  let bs := l.blades W.n
  x.toList.zipIdx.map fun (c, i) => (bs[i]!, c)

/-- An element of layout `l` of `W` printed as Julia prints it in a **compact**
context (the coefficient of a nested chain): `1v₁+2v₂+3v₃`, `1+2v₁₂`, `0+1v₁`, `1v⃖`. -/
def innerCompact {n : Nat} (W : TensorBundle) (l : Layout) (x : Values α n) : String :=
  let ts := terms W l x
  match l, ts with
  | .even, (_, s) :: rest =>
    JuliaShow.printIO true s ++ String.join (rest.map fun (b, c) => JuliaShow.showTerm true true c ++ W.bladeLabel b)
  | .full, (_, s) :: rest =>
    let nz := rest.filter fun (_, c) => !Coeff.isZero c
    if nz.isEmpty then JuliaShow.printIO true s ++ JuliaShow.showStar s ++ "v⃖"
    else JuliaShow.printIO true s ++ String.join (nz.map fun (b, c) => JuliaShow.showTerm true true c ++ W.bladeLabel b)
  | _, (b, c) :: rest =>
    JuliaShow.showValue true c ++ W.bladeLabel b ++
      String.join (rest.map fun (b, c) => JuliaShow.showTerm true true c ++ W.bladeLabel b)
  | _, [] => ""

/-- The 2-arg Julia `show` of a nested element: outer layout `ld` of `V` whose
coefficients are the inner strings `cols` (already printed compactly) with their
zero test `isZero`. -/
def outer (V : TensorBundle) (ld : Layout) (cols : List (String × Bool)) : String :=
  let bs := ld.blades V.n
  let lab := fun (i : Nat) => V.bladeLabel bs[i]!
  let paren := fun (s : String) (i : Nat) => "(" ++ s ++ ")" ++ lab i
  let indexed := cols.zipIdx
  match ld, indexed with
  | .even, ((s, _), _) :: rest => s ++ String.join (rest.map fun ((c, _), i) => " + " ++ paren c i)
  | .full, ((s, _), _) :: rest =>
    let nz := rest.filter fun ((_, z), _) => !z
    if nz.isEmpty then s ++ "⊗v⃖" else s ++ String.join (nz.map fun ((c, _), i) => " + " ++ paren c i)
  | _, ((s, _), i) :: rest => paren s i ++ String.join (rest.map fun ((c, _), j) => " + " ++ paren c j)
  | _, [] => ""

/-! ## `print_matrix` -/

/-- A matrix cell: its printed string and Julia's `alignment` pair `(left, right)`. -/
structure Cell where
  /-- The printed cell. -/
  str : String
  /-- Julia `alignment(io, x)`: widths left and right of the alignment point. -/
  align : Nat × Nat
  deriving Inhabited

/-- A number or basis blade cell (Julia `alignment(io, x::Number)`): right-aligned. -/
def Cell.number (s : String) : Cell := ⟨s, (textwidth s, 0)⟩

/-- A real cell (Julia `alignment(io, x::Real)`): split at the first `.`, `e`,
`E`, `f` or `F`. -/
def Cell.real (s : String) : Cell :=
  let cs := s.toList
  let k := (cs.findIdx? fun c => c == '.' || c == 'e' || c == 'E' || c == 'f' || c == 'F').getD cs.length
  ⟨s, (textwidth (String.ofList (cs.take k)), textwidth (String.ofList (cs.drop k)))⟩

/-- A complex cell (Julia `alignment(io, x::Complex)`, regex `^(.*[^ef][\+\-])(.*)$`):
split after the last `+`/`-` that follows a character other than `e`/`f`. -/
def Cell.complex (s : String) : Cell :=
  let cs := s.toList.toArray
  let idx := (List.range cs.size).reverse.find? fun i =>
    i ≥ 1 && (cs[i]! == '+' || cs[i]! == '-') && cs[i - 1]! != 'e' && cs[i - 1]! != 'f'
  match idx with
  | some i => ⟨s, (textwidth (String.ofList (cs.toList.take (i + 1))), textwidth (String.ofList (cs.toList.drop (i + 1))))⟩
  | none => ⟨s, (textwidth s, 0)⟩

/-- How a coefficient type aligns in Julia's `print_matrix` (and prints there, in
a compact context). -/
class MatrixCell (α : Type) where
  /-- The cell of a value. -/
  cell : α → Cell

instance : MatrixCell Int := ⟨fun x => Cell.number (toString x)⟩
instance : MatrixCell Nat := ⟨fun x => Cell.number (toString x)⟩
instance : MatrixCell Float := ⟨fun x => Cell.real (F64.showIO true x)⟩
instance : MatrixCell Rat := ⟨fun x =>
  let s := JuliaShow.showIO true x
  -- Julia `alignment(io, x::Rational)`: split at the first `/`
  let cs := s.toList
  let k := (cs.findIdx? (· == '/')).getD cs.length
  ⟨s, (textwidth (String.ofList (cs.take k)), textwidth (String.ofList (cs.drop k)))⟩⟩
instance : MatrixCell (Complex Float) := ⟨fun z => Cell.complex (showComplex true z)⟩

/-- Julia `print_matrix(io, X)` with `pre = " "`, `sep = "  "` (`arrayshow.jl`):
columns aligned on the maxima of the cells' alignment pairs, no right padding
on the last column, rows joined by newlines. -/
def printMatrix (rows : Array (Array Cell)) : String :=
  let ncols := rows.foldl (fun m r => max m r.size) 0
  let A := (List.range ncols).map fun k =>
    rows.foldl (fun (L, R) r => match r[k]? with
      | some c => (max L c.align.1, max R c.align.2)
      | none => (L, R)) (0, 0)
  let A := A.toArray
  let row := fun (r : Array Cell) =>
    " " ++ String.join ((List.range r.size).map fun k =>
      let c := r[k]!
      let (L, R) := A[k]!
      let l := "".pushn ' ' (L - c.align.1)
      let rpad := if k + 1 == r.size then "" else "".pushn ' ' (R - c.align.2)
      l ++ c.str ++ rpad ++ (if k + 1 < r.size then "  " else ""))
  "\n".intercalate (rows.toList.map row)

/-- Julia `display_matrix` (`forms.jl:365-372`) of an `r × c` table: the domain
pseudoscalar and the domain blades on top, the codomain blades on the left. -/
def displayCells (V : TensorBundle) (ld : Layout) (W : TensorBundle) (lc : Layout)
    (entry : Nat → Nat → Cell) : Array (Array Cell) :=
  let dom := ld.blades V.n
  let cod := lc.blades W.n
  let header := #[Cell.number (V.bladeLabel (DirectSum.Bits.lowMask V.n))] ++ dom.map (Cell.number ∘ V.bladeLabel)
  #[header] ++ (Array.range cod.size).map fun i =>
    #[Cell.number (W.bladeLabel cod[i]!)] ++ (Array.range dom.size).map fun j => entry i j

/-- Julia's type name of a coefficient type in a summary. -/
class JuliaTypeName (α : Type) where
  /-- `Int64`, `Float64`, ... -/
  name : String

instance : JuliaTypeName Int := ⟨"Int64"⟩
instance : JuliaTypeName Float := ⟨"Float64"⟩
instance : JuliaTypeName Rat := ⟨"Rational{Int64}"⟩
instance : JuliaTypeName (Complex Float) := ⟨"ComplexF64"⟩

/-- Julia's type of a nested element: `Chain{V, G, T, N}`, `Simplex{V, T, N}`
(grade-1 outer chains), `Spinor{V, T, N}`, `CoSpinor{V, T, N}`, `Multivector{V, T, N}`. -/
def typeName (V : TensorBundle) (l : Layout) (inner : String) (outerChain : Bool) : String :=
  let N := toString (l.size V.n)
  match l with
  | .chain 1 => if outerChain then s!"Simplex\{{V}, {inner}, {N}}" else s!"Chain\{{V}, 1, {inner}, {N}}"
  | .chain g => s!"Chain\{{V}, {g}, {inner}, {N}}"
  | .even => s!"Spinor\{{V}, {inner}, {N}}"
  | .odd => s!"CoSpinor\{{V}, {inner}, {N}}"
  | .full => s!"Multivector\{{V}, {inner}, {N}}"

end Forms.Show

open Forms.Show

namespace TensorOperator

variable {V W : TensorBundle} {ld lc : Layout} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia's 2-arg `show` of an operator (`forms.jl:667`: the nested value). -/
def showJulia (T : TensorOperator V ld W lc α) : String :=
  outer V ld ((List.finRange (ld.size V.n)).map fun j =>
    let c := T.colValues j
    (innerCompact W lc c, c.all Coeff.isZero))

instance : ToString (TensorOperator V ld W lc α) := ⟨showJulia⟩

/-- Julia's `summary(T)` (`forms.jl:662-665`): `R×C` and the type. -/
def summary [JuliaTypeName α] (T : TensorOperator V ld W lc α) : String :=
  let inner := typeName W lc (JuliaTypeName.name α) false
  let outerT := typeName V ld inner true
  let kind := if V == W && ld == lc then s!"Endomorphism\{{V}, {outerT}}"
    else s!"TensorOperator\{{V}, {W}, {outerT}}"
  s!"{T.rows}×{T.cols} {kind}"

/-- The body of Julia's 3-arg `show` (`forms.jl:669-710`): `print_matrix` of
`display_matrix(T)`. -/
def displayBody [MatrixCell α] (T : TensorOperator V ld W lc α) : String :=
  printMatrix (displayCells V ld W lc fun i j => MatrixCell.cell (T.entry i j))

/-- Julia's 3-arg `show(io, MIME"text/plain", T)`: the summary, `:` and the matrix. -/
def display [MatrixCell α] [JuliaTypeName α] (T : TensorOperator V ld W lc α) : String :=
  T.summary ++ ":\n" ++ T.displayBody

/-- The cells of Julia's `print(data[j,i])` in `printtex` (non-compact 2-arg
`print`), with Julia's subscript replacement (`forms.jl:1745-1760`). -/
def texCells (T : TensorOperator V ld W lc α) : Array (Array String) :=
  let dom := ld.blades V.n
  let cod := lc.blades W.n
  #[#[V.bladeLabel (DirectSum.Bits.lowMask V.n)] ++ dom.map V.bladeLabel] ++
    (Array.range cod.size).map fun i =>
      #[W.bladeLabel cod[i]!] ++ (Array.range dom.size).map fun j => JuliaShow.printIO false (T.entry i j)

end TensorOperator

namespace Forms.Show

/-- Julia `subscrepl` and `printtex(data)` (`forms.jl:1731-1756`): cells joined by
` & ` (Julia compares the column index with the *row* count, so the separator
logic is only right for square tables; kept), rows by ` \\` and a newline,
subscripts turned into `_{…}` and consecutive subscripts merged. -/
def printtex (cells : Array (Array String)) : String :=
  let n := cells.size
  let m := (cells[0]?.map (·.size)).getD 0
  let raw := String.join <| (List.range n).map fun j =>
    let row := cells[j]!
    String.join ((List.range m).map fun i =>
        (row[i]?.getD "") ++ (if i + 1 != n then " & " else "")) ++
      (if j + 1 != m then " \\\\\n" else "")
  let repl := fun (c : Char) => (match c with
    | '∞' => "_{\\infty}" | '∅' => "_{\\emptyset}" | '𝟎' => "0"
    | '₀' => "_{0}" | '₁' => "_{1}" | '₂' => "_{2}" | '₃' => "_{3}" | '₄' => "_{4}"
    | '₅' => "_{5}" | '₆' => "_{6}" | '₇' => "_{7}" | '₈' => "_{8}" | '₉' => "_{9}"
    | c => c.toString : String)
  (String.join (raw.toList.map repl)).replace "}_{" ""

end Forms.Show

/-- Julia `printtex(E::Endomorphism)` (`forms.jl:1760`). -/
def TensorOperator.printtex {V W : TensorBundle} {ld lc : Layout} {α : Type} [Coeff α] [JuliaShow α]
    (T : TensorOperator V ld W lc α) : String :=
  Forms.Show.printtex T.texCells

/-! ## Cayley tables -/

namespace CayleyTable

variable {V : TensorBundle}

/-- Julia's `show` of a blade-level result (`Submanifold`, `Single`, `Zero`, or a
sum printed as a multivector). -/
def showEntry (V : TensorBundle) : Except String BladeResult → String
  | .error e => e
  | .ok .zero => "𝟎"
  | .ok (.blade b) => V.bladeLabel b
  | .ok (.single c b) => V.showTerm c b (c.den != 1)
  | .ok (.sum ts) =>
    let parts := ts.toList.zipIdx.map fun ((b, c), i) =>
      let s := V.showTerm c b (c.den != 1)
      if i == 0 then s else if s.startsWith "-" then " - " ++ (s.drop 1).toString else " + " ++ s
    String.join parts
  | .ok (.nested _ r) => showEntry V (.ok r)

/-- The TeX cells of the table (`display_matrix` of the Cayley operator). -/
def texCells (C : CayleyTable V) : Array (Array String) :=
  let bs := C.layout.blades V.n
  #[#[V.bladeLabel (DirectSum.Bits.lowMask V.n)] ++ bs.map V.bladeLabel] ++
    (Array.range bs.size).map fun i => #[V.bladeLabel bs[i]!] ++ (C.entries[i]!).map (showEntry V)

/-- Julia `printtex(cayley(V, op))`. -/
@[inline] def printtex (C : CayleyTable V) : String := Forms.Show.printtex C.texCells

/-- The body of Julia's 3-arg display of the table (entries are `Number`s:
right-aligned). -/
def displayBody (C : CayleyTable V) : String :=
  printMatrix (displayCells V C.layout V C.layout fun i j =>
    Cell.number (showEntry V ((C.entries[i]?.bind (·[j]?)).getD (.ok .zero))))

end CayleyTable

/-- Julia `alltex(V, ops=[∧,∨,<,>,<<,>>])` (`forms.jl:1762-1764`). -/
def alltex (V : TensorBundle)
    (ops : List BinOp := [.wedge, .vee, .contractionLeft, .contraction, .contractionRevLeft,
      .contractionRevRight]) : List String :=
  ops.map fun op => (cayley V op).printtex

/-! ## Rank-one forms -/

namespace Projector

variable {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `show(::Proj)` for a real `λ` (`forms.jl:427`): `λProj(v)`, the `λ`
omitted when it is one. -/
def showJulia [BEq α] (P : Projector V G α) : String :=
  (if P.lam == Coeff.one then "" else JuliaShow.printIO false P.lam) ++ "Proj(" ++ toString P.v ++ ")"

instance [BEq α] : ToString (Projector V G α) := ⟨showJulia⟩

end Projector

namespace SpectralOperator

variable {V : TensorBundle} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `show(::Proj)` of a spectral operator (`forms.jl:428`): `(λ)Proj(v)`
with the eigenvalue chain and the chain of eigenvectors. -/
def showJulia (S : SpectralOperator V α) : String :=
  "(" ++ toString (⟨S.vals⟩ : Chain V 1 α) ++ ")Proj(" ++ S.vecs.showJulia ++ ")"

instance : ToString (SpectralOperator V α) := ⟨showJulia⟩

end SpectralOperator

namespace Dyadic

variable {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `show(::Dyadic)` (`forms.jl:464`): `(x)⊗(y)`. -/
def showJulia (D : Dyadic V G W H α) : String := "(" ++ toString D.x ++ ")⊗(" ++ toString D.y ++ ")"

instance : ToString (Dyadic V G W H α) := ⟨showJulia⟩

end Dyadic

namespace DiagonalOperator

variable {V : TensorBundle} {l : Layout} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia's `summary(D)` (`forms.jl:543`): `n×n DiagonalMorphism{V, Chain{V, 1, T, n}}`
(`DiagonalOutermorphism` for a multivector diagonal, `DiagonalOperator` otherwise). -/
def summary [JuliaTypeName α] (_ : DiagonalOperator V l α) : String :=
  let N := l.size V.n
  let inner := Forms.Show.typeName V l (JuliaTypeName.name α) false
  let kind := match l with
    | .chain 1 => "DiagonalMorphism"
    | .full => "DiagonalOutermorphism"
    | _ => "DiagonalOperator"
  s!"{N}×{N} {kind}\{{V}, {inner}}"

/-- Julia `show(::DiagonalOperator)` (`forms.jl:545`): as the materialised operator. -/
instance : ToString (DiagonalOperator V l α) := ⟨fun D => D.toOperator.showJulia⟩

/-- The body of Julia's 3-arg display (`forms.jl:547-553`). -/
def displayBody [MatrixCell α] (D : DiagonalOperator V l α) : String := D.toOperator.displayBody

end DiagonalOperator

namespace Outermorphism

variable {V W : TensorBundle} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia's `summary(O)` (`forms.jl:790`): `2ᵐ×2ⁿ Outermorphism{V, Tuple{…}}` with the
type of every stored compound. -/
def summary [JuliaTypeName α] (O : Outermorphism V W α) : String :=
  let T := JuliaTypeName.name α
  let blockType := fun (g : Nat) =>
    let inner := Forms.Show.typeName W (.chain g) T false
    Forms.Show.typeName V (.chain g) inner true
  let blocks := (List.range O.blocks.size).map fun k => blockType (k + 1)
  s!"{2 ^ W.n}×{2 ^ V.n} Outermorphism\{{V}, Tuple\{{", ".intercalate blocks}}}"

/-- Julia `show(::Outermorphism)` (`forms.jl:792`): as the full block matrix. -/
instance : ToString (Outermorphism V W α) := ⟨fun O => O.toOperator.showJulia⟩

/-- The body of Julia's 3-arg display (`forms.jl:794-800`). -/
def displayBody [MatrixCell α] (O : Outermorphism V W α) : String := O.toOperator.displayBody

end Outermorphism

end Grassmann
