import Tests.Forms.Common

/-!
# Exact operator algebra against Julia (`oracle/golden/forms/exact.json`)

Integer endomorphisms of `ℝⁿ`, `n = 1 … 6`: the determinant family (`det`, `∧`, every
compound, adjugate, cofactor, `characteristic_exact`), the outermorphism and its action on
every grade and on the even/odd/full algebra, products, sums, uniform scalings,
application, row application, bilinear forms, Gershgorin radii, Lie brackets, `bivector`,
`pfaffian`, and Julia's 2-arg and 3-arg display. All exact (`Int`), except the Pfaffian in
dimension ≥ 4, which Julia divides by `k!` (a float: compared bit for bit).
-/

namespace Tests.FormsTests.Exact

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- One golden case. -/
def check (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let rowsA := intRows (fld c "A")
  let n := rowsA.length
  let V := En n
  let A : Endomorphism V (.chain 1) Int := endo V rowsA
  let B : Endomorphism V (.chain 1) Int := endo V (intRows (fld c "B"))
  let x : Chain V 1 Int := chainOf V 1 (ints (fld c "x"))
  let y : Chain V 1 Int := chainOf V 1 (ints (fld c "y"))
  let w := fun (s : String) => fun (_ : Unit) => s!"case {k} (n={n}) {s}"
  let mut t := t
  t := t.num .bits (.int A.det) (fld c "det") (w "det")
  t := t.nums .bits (vals A.wedgeAll.v) (fld c "wedge") (w "∧")
  t := t.num .bits (.int A.tr) (fld c "tr") (w "tr")
  let cs := arr (fld c "compound")
  for g in [0:n + 1] do
    t := t.mat .bits (opRows (A.compound g)) (cs[g]!) (w s!"compound {g}")
  -- Julia's adjugate/cofactor of a 1×1 matrix is its inverse `1/a` (`composite.jl:797, 806`);
  -- the classical adjugate `[1]` here
  if n ≥ 2 then
    t := t.mat .bits (opRows A.adjugate) (fld c "adjugate") (w "adjugate")
    t := t.mat .bits (opRows A.cofactor) (fld c "cofactor") (w "cofactor")
  else
    t := t.ok (A.adjugate.toRows == [[1]] && A.cofactor.toRows == [[1]]) (w "1×1 adjugate = [1]")
  t := t.nums .bits (vals A.characteristicExact.v) (fld c "charexact") (w "characteristic_exact")
  let O := A.outermorphism
  t := t.mat .bits (opRows O.toOperator) (fld c "outer") (w "outermorphism")
  t := t.num .bits (.int O.tr) (fld c "outertr") (w "tr(O)")
  t := t.mat .bits (opRows A.transpose) (fld c "transpose") (w "transpose")
  t := t.mat .bits (opRows (A * B)) (fld c "mul") (w "T*U")
  t := t.mat .bits (opRows (A + B)) (fld c "add") (w "T+U")
  t := t.mat .bits (opRows (A - B)) (fld c "sub") (w "T-U")
  t := t.mat .bits (opRows (A + AbstractTensors.UniformScaling.mk (1 : Int))) (fld c "plusI") (w "T+I")
  t := t.mat .bits (opRows (AbstractTensors.UniformScaling.mk (2 : Int) - A)) (fld c "twoIminus") (w "2I-T")
  t := t.nums .bits (vals (A x).v) (fld c "apply") (w "T(x)")
  t := t.nums .bits (vals (x ⋅ A : Chain V 1 Int).v) (fld c "rowapply") (w "x⋅T")
  t := t.num .bits (.int (A.form x y)) (fld c "form") (w "T(x,y)")
  t := t.nums .bits (vals A.gerschgorin) (fld c "gerschgorin") (w "gerschgorin")
  t := t.nums .bits (vals A.diagValues) (fld c "diag") (w "diag")
  t := t.mat .bits (opRows (lieBracket [A, B])) (fld c "lie2") (w "𝓛[T,U]")
  t := t.mat .bits (opRows (lieBracket [A, B, A * B])) (fld c "lie3") (w "𝓛[T,U,TU]")
  if n ≥ 2 then
    t := t.mat .bits (opRows ((A.compound 2) * (B.compound 2))) (fld c "compoundmul") (w "Λ²T Λ²U")
    t := t.nums .bits (vals (Endomorphism.bivector A).v) (fld c "bivector") (w "bivector")
    -- Julia divides by `k!` only for `k = ⌊n/2⌋ ≥ 2` (a float result)
    if n ≤ 3 then
      t := t.nums .bits (vals (Endomorphism.pfaffian A).v) (fld c "pfaffian") (w "pfaffian")
    else
      let pf := Endomorphism.pfaffian (A.map (fun (z : Int) => Float.ofInt z))
      t := t.nums .bits (vals pf.v) (fld c "pfaffian") (w "pfaffian")
  t := t.str A.showJulia (fld c "show") (w "show")
  t := t.str A.displayBody (fld c "display") (w "display")
  t := t.str A.summary (fld c "summary") (w "summary")
  t := t.str O.summary (fld c "summaryOuter") (w "summary(O)")
  if n ≥ 2 then t := t.str (A.compound 2).summary (fld c "summaryCompound") (w "summary(Λ²T)")
  t := t.str A.printtex (fld c "printtex") (w "printtex")
  if n ≤ 4 then
    t := t.str O.displayBody (fld c "displayOuter") (w "display(O)")
    t := t.str (toString O) (fld c "showOuter") (w "show(O)")
  if n ≤ 4 && n ≥ 2 then
    t := t.str (A.compound 2).displayBody (fld c "displayCompound") (w "display(Λ²T)")
  if n == 1 then
    t := t.skip  -- (the 1×1 adjugate golden, see above)
  -- the outermorphism on every grade and on the halves / full algebra (2 ≤ n ≤ 5)
  if 2 ≤ n && n ≤ 5 then
    let M : Multivector V Int := mvOf V (ints (fld c "m"))
    t := t.nums .bits (vals (O * M : Multivector V Int).v) (fld c "outerMV") (w "O(M)")
    let ev : Spinor V Int := M.half false
    let od : CoSpinor V Int := M.half true
    -- in 2D Julia's `even(M)` is a `Couple`, whose image is a `Multivector`
    let img : Spinor V Int := O * ev
    if (arr (fld c "outerSpinor")).size == 2 ^ n then
      t := t.nums .bits (vals (toMultivector img).v) (fld c "outerSpinor") (w "O(even M)")
    else
      t := t.nums .bits (vals img.v) (fld c "outerSpinor") (w "O(even M)")
    t := t.nums .bits (vals (O * od : CoSpinor V Int).v) (fld c "outerCoSpinor") (w "O(odd M)")
    let oc := arr (fld c "outerChains")
    for g in [1:n + 1] do
      let img := O.applyValues (.chain g) (M.grade g).v
      t := t.nums .bits (vals img) (oc[g - 1]!) (w s!"O(M(g={g}))")
    t := t.mat .bits (opRows (O * B.outermorphism).toOperator) (fld c "outerOuter") (w "O⋅O'")
    t := t.mat .bits (opRows O.adjugate.toOperator) (fld c "outerAdj") (w "adjugate(O)")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "exact"
  return (cases j).toList.zipIdx.foldl (fun t (c, k) => check t c k) (Tally.new "forms/exact")

end Tests.FormsTests.Exact
