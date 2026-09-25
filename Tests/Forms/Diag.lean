import Tests.Forms.Common

/-!
# Diagonal operators and non-square operators against Julia

* `diag.json`: `DiagonalOperator(Chain{V,1}(d…))` and its outermorphism: trace,
  determinant, `∧`, compounds, adjugates, inverses, `exp`, application to vectors and to
  the full / even algebra, `D ⋅ T`, the characteristic polynomial (exact), `eigpolys`,
  `eigvals` (closed-form roots: `rtol = 1e-12`), `sylvester`, `eigmults`, `scalar`, `D/2`
  (through the reciprocal) and the display. Julia's `D ⋅ AntiSpinor` (even part) and
  `T ⋅ D` (transposed) are defective and not generated.
* `rect.json`: non-square grade-1 operators (`m × n`): application, `∧`, compounds, the
  outermorphism (its `2ᵐ × 2ⁿ` matrix and its action on a multivector, with zero padding),
  the Moore-Penrose inverse (`rtol = 1e-12`: Julia's reciprocal frame for fewer columns),
  transpose and display.
-/

namespace Tests.FormsTests.DiagSuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- One diagonal case. -/
def diagCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let dv := ints (fld c "d")
  let n := dv.length
  let V := En n
  let D : DiagonalMorphism V Int := ⟨Values.ofFn fun i => dv[i.1]!⟩
  let Df : DiagonalMorphism V Float := D.map Float.ofInt
  let OD := DiagonalMorphism.outermorphism D
  let x : Chain V 1 Int := chainOf V 1 (ints (fld c "x"))
  let M : Multivector V Int := mvOf V (ints (fld c "m"))
  let A : Endomorphism V (.chain 1) Int := endo V (intRows (fld c "A"))
  let w := fun (s : String) => fun (_ : Unit) => s!"diag case {k} d={dv} {s}"
  let mut t := t
  t := t.num .bits (.int D.tr) (fld c "tr") (w "tr")
  t := t.num .bits (.int (DiagonalMorphism.det D)) (fld c "det") (w "det")
  t := t.nums .bits (vals (DiagonalMorphism.wedgeAll D).v) (fld c "wedge") (w "∧")
  if n ≥ 2 then t := t.nums .bits (vals (DiagonalMorphism.compound D 2).d) (fld c "compound2") (w "compound 2")
  t := t.nums .bits (vals OD.d) (fld c "outer") (w "outermorphism")
  t := t.nums .bits (vals (DiagonalMorphism.adjugate D).d) (fld c "adjugate") (w "adjugate")
  t := t.nums .bits (vals (DiagonalOutermorphism.adjugate OD).d) (fld c "outerAdj") (w "adjugate(O)")
  t := t.nums .bits (vals (DiagonalMorphism.inv Df).d) (fld c "inv") (w "inv")
  t := t.nums .bits (vals (DiagonalMorphism.exp Df).d) (fld c "exp") (w "exp")
  t := t.nums .bits (vals (DiagonalOutermorphism.inv (DiagonalMorphism.outermorphism Df)).d) (fld c "outerInv") (w "inv(O)")
  t := t.nums .bits (vals (D * x : Chain V 1 Int).v) (fld c "apply") (w "D(x)")
  t := t.num .bits (.int (D.form x x)) (fld c "form") (w "D(x,x)")
  t := t.nums .bits (vals (DiagonalOutermorphism.apply OD M : Multivector V Int).v) (fld c "outerMV") (w "O(M)")
  let ev : Spinor V Int := M.half false
  let img : Spinor V Int := DiagonalOutermorphism.apply OD ev
  if (arr (fld c "outerSpinor")).size == 2 ^ n then
    t := t.nums .bits (vals (toMultivector img).v) (fld c "outerSpinor") (w "O(even M)")
  else
    t := t.nums .bits (vals img.v) (fld c "outerSpinor") (w "O(even M)")
  if n ≥ 2 then
    t := t.nums .bits (vals (DiagonalOutermorphism.apply OD (M.grade 2) : Chain V 2 Int).v) (fld c "outerChain2") (w "O(M(2))")
  t := t.mat .bits (opRows (D * A)) (fld c "DT") (w "D⋅T")
  t := t.nums .bits (vals D.characteristic.v) (fld c "charexact") (w "characteristic")
  t := t.nums .bits (vals Df.eigpolys.v) (fld c "eigpolys") (w "eigpolys")
  match Df.eigvals with
  | .real v => t := t.nums (.approx 1e-12) (vals v) (fld c "eigvals") (w "eigvals")
  | .complex v => t := t.nums (.approx 1e-12) (vals v) (fld c "eigvals") (w "eigvals")
  match Df.sylvester with
  | .real v => t := t.nums (.approx 1e-12) (vals v) (fld c "sylvester") (w "sylvester")
  | .complex v => t := t.nums (.approx 1e-12) (vals v) (fld c "sylvester") (w "sylvester")
  t := t.nums .bits (vals (Forms.eigmultsValues D.d)) (fld c "eigmults") (w "eigmults")
  t := t.num .bits (.flt Df.scalar) (fld c "scalar") (w "scalar")
  t := t.nums .bits (vals (Df / (2 : Float)).d) (fld c "half") (w "D/2")
  t := t.str (toString D) (fld c "show") (w "show")
  t := t.str (toString OD) (fld c "showOuter") (w "show(O)")
  t := t.str D.displayBody (fld c "display") (w "display")
  return t

/-- One non-square case (`m × n`). -/
def rectCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let rowsA := intRows (fld c "A")
  let m := rowsA.length
  let n := (rowsA.headD []).length
  let V := En n
  let W := En m
  let A : Simplex V W Int := (TensorOperator.ofRows? rowsA).getD TensorOperator.zero
  let Af : Simplex V W Float := A.map Float.ofInt
  let x : Chain V 1 Int := chainOf V 1 (ints (fld c "x"))
  let w := fun (s : String) => fun (_ : Unit) => s!"rect case {k} ({m}×{n}) {s}"
  let mut t := t
  t := t.nums .bits (vals (A * x : Chain W 1 Int).v) (fld c "apply") (w "A x")
  if n > m then t := t.nums .bits (vals A.wedgeAllWide.v) (fld c "wedge") (w "∧")
  else t := t.nums .bits (vals A.wedgeAll.v) (fld c "wedge") (w "∧")
  let cs := arr (fld c "compound")
  for g in [1:min m n + 1] do
    t := t.mat .bits (opRows (A.compound g)) (cs[g - 1]!) (w s!"compound {g}")
  let O := A.outermorphism
  t := t.mat .bits (opRows O.toOperator) (fld c "outer") (w "outermorphism")
  let M : Multivector V Int := mvOf V (ints (fld c "mv"))
  let OM : Multivector W Int := O * M
  -- Julia applies a non-square compound `Λᵍ T` (g ≥ 2, more than one domain blade) through
  -- the generic metric contraction (`products.jl:1165`), which flips its sign; the port
  -- applies the compound matrix (so `O(v₁ ∧ v₂) = T v₁ ∧ T v₂`, checked below). The scalar
  -- and vector parts are compared with Julia, the rest with the outermorphism property.
  let jl := ints (fld c "outerMV")
  let low := 1 + m
  t := t.ok ((OM.v.toList.take low) == jl.take low) (w s!"O(M) grades 0-1: {OM.v.toList} vs {jl}")
  for g in [2:min m n + 1] do
    for bi in (Leibniz.indexBasis n g).toList do
      let idx := (DirectSum.Bits.indices bi).toList
      let imgs := idx.map fun i => (Chain.ofFn fun r => A.entry r.1 (i - 1) : Chain W 1 Int)
      let wedge : Chain W imgs.length Int := wedgeVectors imgs
      let e : Multivector V Int := Multivector.ofFn fun k => if (Leibniz.indexBasisAll n)[k.1]! == bi then 1 else 0
      let viaO : Multivector W Int := O * e
      t := t.ok (viaO.v.toList == (toMultivector wedge).v.toList) (w s!"O(e_I) = ∧ T eᵢ for I = {idx}")
  t := t.mat (.approx 1e-12) (opRows Af.inv) (fld c "pinv") (w "pinv")
  t := t.mat .bits (opRows A.transpose) (fld c "transpose") (w "transpose")
  t := t.str A.displayBody (fld c "display") (w "display")
  t := t.str A.showJulia (fld c "show") (w "show")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let jd ← load "diag"
  let t := (cases jd).toList.zipIdx.foldl (fun t (c, k) => diagCase t c k) (Tally.new "forms/diag+rect")
  let jr ← load "rect"
  return (cases jr).toList.zipIdx.foldl (fun t (c, k) => rectCase t c k) t

end Tests.FormsTests.DiagSuite
