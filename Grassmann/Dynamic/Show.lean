/-
Julia display of dynamic elements (`show`, `repr`, and `show` in an `IOContext`
with `:compact => true`; port-notes/grassmann-types.md §5, DESIGN.md §6).

`showIO compact x` is Julia `sprint(show, x; context = :compact => compact)`:

| kind | rule (Grassmann.jl `src/multivectors.jl`) |
|---|---|
| `Zero`, `Infinity` | `𝟎`, `∞` (DirectSum `src/DirectSum.jl:604, 663`) |
| `One`, `Submanifold` | the blade label (`v`, `v₁₂`, `v∞∅`, `w¹`, `∂₁v₁`) |
| `Single` | Leibniz `showvalue`: `2v₁`, `(1//2)v₁`, `NaN*v₁` (DS:488) |
| `Chain` | values in compact form (`compactio`), every term, zeros included (MV:109-116) |
| `Multivector` | `print(v[1])`, then the nonzero terms; `3v⃖` when only the scalar is left (MV:340-356) |
| `Spinor` | `print(v[1])`, then every even-grade term (MV:589-600) |
| `CoSpinor` | every odd-grade term (MV:601-615) |
| `Couple` | `show(re)` then `showterm(B, im)` (MV:757-761) |
| `PseudoCouple` | `showvalue(B, re)` then `showterm(I, im)` (MV:762-766) |
| `Phasor` | `show(amp)`, ` ∠ ` (`∠` when compact), `print(angle)` (MV:931-934) |

The term separators (` + ` vs `+`) follow the caller's `:compact` flag; the values of
`Chain`, `Multivector`, `Spinor` and `CoSpinor` always print compactly (Grassmann's
`compactio`, 6 significant digits), those of the other kinds follow the caller.
Coefficients print through `JuliaBase.JuliaShow` (Julia's `show` of the scalar
type, Leibniz `showvalue`/`showstar`, Grassmann `showterm`).
-/
import Grassmann.Dynamic.Basic
import Grassmann.Types.Show

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia's `showvalue` for the first term and `showterm` for the others, values in
compact form (Grassmann `compactio`), separators by `compact`. -/
def showTerms (V : TensorBundle) (compact : Bool) (ts : List (UInt64 × α)) : String :=
  String.join <| ts.zipIdx.map fun ((b, x), i) =>
    (if i == 0 then JuliaShow.showValue true x else JuliaShow.showTerm compact true x) ++ V.bladeLabel b

/-- `print(io, v[1])` followed by `showterm` of the given terms (Multivector, Spinor). -/
def showScalarThen (V : TensorBundle) (compact : Bool) (s : α) (ts : List (UInt64 × α)) : String :=
  JuliaShow.printIO true s ++ String.join (ts.map fun (b, x) => JuliaShow.showTerm compact true x ++ V.bladeLabel b)

/-- Julia `show(io, x)` of a dynamic element in a context with `:compact => compact`. -/
def showIO (compact : Bool) : TA V α → String
  | zero => "𝟎"
  | one => V.bladeLabel 0
  | infinity => "∞"
  | blade b => V.bladeLabel b
  | single b x => JuliaShow.showValue compact x ++ V.bladeLabel b
  | chain g c => showTerms V compact (layoutTerms V (.chain g) c.v)
  | multi m =>
    let s := getD m.v 0
    let rest := (layoutTerms V .full m.v).drop 1 |>.filter (fun (_, x) => !Coeff.isZero x)
    if rest.isEmpty then JuliaShow.printIO true s ++ JuliaShow.showStar s ++ "v⃖"
    else showScalarThen V compact s rest
  | spinor h => match layoutTerms V (halfLayout false) h.v with
    | (_, s) :: rest => showScalarThen V compact s rest
    | [] => ""
  | cospinor h => showTerms V compact (layoutTerms V (halfLayout true) h.v)
  | couple b re im =>
    JuliaShow.showIO compact re ++ JuliaShow.showTerm compact compact im ++ V.bladeLabel b
  | pseudo b re im =>
    JuliaShow.showValue compact re ++ V.bladeLabel b ++ JuliaShow.showTerm compact compact im ++
      V.bladeLabel (pseudoBits V)
  | phasor amp θ => JuliaShow.showIO compact amp ++ (if compact then "∠" else " ∠ ") ++ showIO compact θ

/-- Julia `repr(x)` (`sprint(show, x)`). -/
@[inline] def showString (x : TA V α) : String := showIO false x

/-- Julia `repr(x; context = :compact => true)`. -/
@[inline] def showCompact (x : TA V α) : String := showIO true x

instance : ToString (TA V α) := ⟨showString⟩

instance : Repr (TA V α) := ⟨fun x _ => showString x⟩

end TA

end Grassmann
