/-
Julia display of the typed elements (`show`, `repr`; Grassmann.jl
`src/multivectors.jl:46-58, 109-116, 340-356, 589-615, 757-766`, DirectSum.jl
`src/DirectSum.jl:488`; port-notes/grassmann-types.md §5.2-5.4, DESIGN.md §6).

The coefficient printing is `JuliaBase.JuliaShow` (`showValue` = Leibniz
`showvalue`, `showTerm` = Grassmann `showterm`), the blade labels are
`TensorBundle.bladeLabel`. The caller context is non-compact (Julia `repr`);
`Chain`, `Multivector`, `Spinor` and `CoSpinor` print their coefficients through
`compactio` (6 significant digits), the single-term types do not.

| type | rule |
|---|---|
| `Chain` | every term, zeros included: `1v₁ + 0v₂ - 3v₃` |
| `Multivector` | `print(v[1])`, then the nonzero terms; `0v⃖` / `3v⃖` when only the scalar is nonzero |
| `Spinor` | `print(v[1])`, then every even-grade term: `1 + 0v₁₂ + 2v₁₃ + 0v₂₃` |
| `CoSpinor` | every odd-grade term: `1v₁ + 2v₂ + 3v₃ + 4v₁₂₃` |
| `Single` | `2v₁`, `(1//2)v₁` |
| `Couple` | `1 + 2v₁₂` |
| `PseudoCouple` | `1v₁ + 2v₁₂₃` |
-/
import Grassmann.Types.Couple
import JuliaBase.Show

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] [JuliaShow α]

/-- Julia `showvalue` + label of the first term and `showterm` + label of the
others, over `(blade, coefficient)` pairs; coefficients in compact form. -/
def showTermsCompact (V : TensorBundle) (ts : List (UInt64 × α)) : String :=
  String.join <| ts.zipIdx.map fun ((b, x), i) =>
    (if i == 0 then JuliaShow.showValue true x else JuliaShow.showTerm false true x) ++ V.bladeLabel b

/-- The `(blade, coefficient)` pairs of a coefficient vector in layout `l`. -/
def layoutTerms {n : Nat} (V : TensorBundle) (l : Layout) (x : Values α n) : List (UInt64 × α) :=
  let bs := l.blades V.n
  x.toList.zipIdx.map fun (c, i) => (bs[i]!, c)

instance : ToString (Chain V G α) := ⟨fun c => showTermsCompact V (layoutTerms V (.chain G) c.v)⟩

instance : ToString (Multivector V α) where
  toString m :=
    let s := getD m.v 0
    let rest := (layoutTerms V .full m.v).drop 1 |>.filter (fun (_, x) => !Coeff.isZero x)
    if rest.isEmpty then JuliaShow.printIO true s ++ JuliaShow.showStar s ++ "v⃖"
    else JuliaShow.printIO true s ++ String.join (rest.map fun (b, x) =>
      JuliaShow.showTerm false true x ++ V.bladeLabel b)

instance : ToString (Half V p α) where
  toString h :=
    let ts := layoutTerms V (halfLayout p) h.v
    if p then showTermsCompact V ts
    else match ts with
      | (_, s) :: rest => JuliaShow.printIO true s ++ String.join (rest.map fun (b, x) =>
          JuliaShow.showTerm false true x ++ V.bladeLabel b)
      | [] => ""

instance : ToString (Single V G α) := ⟨fun s => JuliaShow.showValue false s.val ++ V.bladeLabel s.bits⟩

instance : ToString (Couple V α) where
  toString z := JuliaShow.showIO false z.re ++ JuliaShow.showTerm false false z.im ++ V.bladeLabel z.bits

instance : ToString (PseudoCouple V α) where
  toString z := JuliaShow.showValue false z.re ++ V.bladeLabel z.bits ++
    JuliaShow.showTerm false false z.im ++ V.bladeLabel (DirectSum.Bits.lowMask V.n)

instance [ToString (Couple V α)] : ToString (Phasor V α) where
  toString z := JuliaShow.showIO false z.amp ++ " ∠ " ++ toString z.angle

end Grassmann
