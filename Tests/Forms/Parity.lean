import Tests.Forms.Common

/-!
# Parity-gap additions to Grassmann.Forms against Julia

Goldens `oracle/golden/forms/{roots2,eigvecs,vandermonde}.json` (`oracle/forms/gen_parity.jl`):

* `roots2.json`: `roots`, `rootsreal`, `rootscomplex` of degree 1-7 (non-monic, divided by
  the leading coefficient) and `monicroots*` of degree ≥ 5 (the companion matrix's
  eigenvalues: LAPACK in Julia, `Forms.Eigen` here, so `rtol = 1e-9` as multisets; the
  closed forms of degree ≤ 4 `rtol = 1e-12`), the real/complex result type exactly, Julia's
  `InexactError`/`DomainError` as errors; constants and complex constant terms.
* `eigvecs.json`: `eigvecs` real-typed exactly when Julia's is, `eigvecsreal` an error
  exactly when Julia's is, and the eigenvectors by residual `‖A v − λ v‖` and unit norm
  (LAPACK leaves the sign free).
* `vandermonde.json`: the Vandermonde operator of a point list (bits), `discriminant`, and the
  least-squares fit `vandermonde(x, y, N)`, `vandermondeinterp`, `approx` (`rtol = 1e-9`: QR
  here, LAPACK's pivoted QR in Julia).
-/

namespace Tests.FormsTests.Parity

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests JuliaBase

/-- The roots checks of one polynomial. -/
def rootsCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let a := flts (fld c "a")
  let w := fun (s : String) => fun (_ : Unit) => s!"roots2 case {k} a={a} {s}"
  let mut t := t
  match a.length with
  | 0 => return t
  | N + 1 =>
    let av : Values Float (N + 1) := Values.ofFn fun i => a[i.1]!
    let m : Mode := if N ≥ 5 then .approx 1e-9 else .approx 1e-12
    let unordered := N ≥ 5
    let jr := fld c "roots"
    if N == 0 then
      t := t.num .bits (.flt (Forms.rootsConst a[0]!)) jr (w "roots of a constant")
      return t
    if N == 1 then
      -- Julia returns a scalar for degree 1
      let z := (Forms.roots av).toList.headD ⟨0, 0⟩
      t := t.num m (.flt z.re) jr (w "roots")
      let zc := (Forms.rootscomplex av).toList.headD ⟨0, 0⟩
      t := t.num m (.cpx zc.re zc.im) (fld c "rootscomplex") (w "rootscomplex")
      match Forms.rootsreal av with
      | .ok v => t := t.num m (.flt (v.toList.headD 0)) (fld c "rootsreal") (w "rootsreal")
      | .error e => t := t.ok false (w s!"rootsreal: {e}")
      return t
    t := t.spectrum m (Forms.roots av) jr (w "roots") unordered
    let mc := fld c "moniccomplex"
    t := if unordered then t.numsSet m (vals (Forms.rootscomplex av)) (fld c "rootscomplex") (w "rootscomplex")
      else t.nums m (vals (Forms.rootscomplex av)) (fld c "rootscomplex") (w "rootscomplex")
    match Forms.rootsreal av, jerr? (fld c "rootsreal") with
    | .ok v, none =>
      t := if unordered then t.numsSet m (vals v) (fld c "rootsreal") (w "rootsreal")
        else t.nums m (vals v) (fld c "rootsreal") (w "rootsreal")
    | .error _, some _ => t := t.ok true (w "rootsreal error")
    | .ok _, some e => t := t.ok false (w s!"rootsreal: Lean ok, Julia {e}")
    | .error e, none => t := t.ok false (w s!"rootsreal: Lean {e}, Julia ok")
    -- the monic entry points on the divided coefficients
    let mv : Values Float N := Forms.monicOf av
    t := t.spectrum m (Forms.monicroots mv) (fld c "monic") (w "monicroots") unordered
    t := if unordered then t.numsSet m (vals (Forms.monicrootscomplex mv)) mc (w "monicrootscomplex")
      else t.nums m (vals (Forms.monicrootscomplex mv)) mc (w "monicrootscomplex")
    match Forms.monicrootsreal mv, jerr? (fld c "monicreal") with
    | .ok v, none =>
      t := if unordered then t.numsSet m (vals v) (fld c "monicreal") (w "monicrootsreal")
        else t.nums m (vals v) (fld c "monicreal") (w "monicrootsreal")
    | .error _, some _ => t := t.ok true (w "monicrootsreal error")
    | .ok _, some e => t := t.ok false (w s!"monicrootsreal: Lean ok, Julia {e}")
    | .error e, none => t := t.ok false (w s!"monicrootsreal: Lean {e}, Julia ok")
    return t

/-- A golden complex scalar. -/
def cplx (j : Json) : Complex Float :=
  match jnum j with
  | some (.cpx a b) => ⟨a, b⟩
  | some (.flt a) => ⟨a, 0⟩
  | _ => ⟨0, 0⟩

/-- A golden float scalar. -/
def flt1 (j : Json) : Float :=
  match jnum j with
  | some (.flt a) => a
  | some (.int a) => Float.ofInt a
  | _ => 0

/-- The eigenvector checks of one matrix. -/
def eigCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let rowsA := floatRows (fld c "A")
  let n := rowsA.length
  let V := En n
  let A : Endomorphism V (.chain 1) Float := endo V rowsA
  let w := fun (s : String) => fun (_ : Unit) => s!"eigvecs case {k} (n={n}) {s}"
  let mut t := t
  let juliaReal := (fld c "eigvecs_real") == .bool true
  let ev := A.eigvecs
  let leanReal := match ev with | .real _ => true | .complex _ => false
  t := t.ok (leanReal == juliaReal) (w s!"eigvecs real-typed: Lean {leanReal}, Julia {juliaReal}")
  match A.eigvecsreal, jerr? (fld c "eigvecsreal") with
  | .ok E, none =>
    -- residuals against the real eigenvalues, unit columns
    let d := A.eigenDecomposition
    for j in [0:n] do
      let lam := d.re.get! j
      let mut res : Float := 0
      let mut nrm : Float := 0
      for i in [0:n] do
        let vi := E.entry i j
        nrm := nrm + vi * vi
        let s := (List.range n).foldl (fun s q => s + A.entry i q * E.entry q j) 0
        res := F64.max res (s - lam * vi).abs
      t := t.ok (res ≤ 1e-9 * F64.max 1 lam.abs) (w s!"eigvecsreal residual {j}: {res}")
      t := t.ok ((nrm - 1).abs ≤ 1e-12) (w s!"eigvecsreal norm {j}: {nrm}")
  | .error _, some _ => t := t.ok true (w "eigvecsreal error")
  | .ok _, some e => t := t.ok false (w s!"eigvecsreal: Lean ok, Julia {e}")
  | .error e, none => t := t.ok false (w s!"eigvecsreal: Lean {e}, Julia ok")
  -- the complex view of `eigvecs` agrees with `eigvecscomplex`
  let C := ev.toComplex
  let D := A.eigvecscomplex
  let same := (List.range (n * n)).all fun q =>
    let a := C.entry (q / n) (q % n)
    let b := D.entry (q / n) (q % n)
    a.re == b.re && a.im == b.im
  t := t.ok same (w "eigvecs as complex = eigvecscomplex")
  return t

/-- The Vandermonde operator of a point list. -/
def vandOp (t : Tally) (c : Json) (k : Nat) : Tally :=
  let x := flts (fld c "x")
  let n := x.length
  let xv : Values Float n := Values.ofFn fun i => x[i.1]!
  let T := Forms.vandermonde xv
  let t := t.mat .bits (opRows T) (fld c "op") fun _ => s!"vandermonde op {k}"
  t.num (.approx 1e-12) (.flt (Forms.discriminantValues xv)) (fld c "disc") fun _ => s!"discriminant {k}"

/-- A least-squares fit. -/
def fitCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  let x : FloatArray := ⟨(flts (fld c "x")).toArray⟩
  let y : FloatArray := ⟨(flts (fld c "y")).toArray⟩
  let N := (fld c "k").getNat?.toOption.getD 0
  let w := fun (s : String) => fun (_ : Unit) => s!"vandermonde fit {k} (m={x.size}, N={N}) {s}"
  let m : Mode := .approx 1e-9
  let rows := Forms.vandermondeRows x N
  let t := t.mat .bits ((List.range x.size).map fun i => (List.range N).map fun j => Num.flt (rows.get! (i * N + j)))
    (fld c "matrix") (w "matrix")
  let coef := Forms.vandermondeFit x y N
  let t := t.nums m (coef.toList.map .flt) (fld c "fit") (w "coefficients")
  let (co, xp, yp) := Forms.vandermondeinterp x y N 8
  let ji := fld c "interp"
  let t := t.nums m (co.toList.map .flt) (fld ji "coef") (w "interp coef")
  let t := t.nums .bits (xp.toList.map .flt) (fld ji "xp") (w "interp grid")
  let t := t.nums (.approx 1e-8) (yp.toList.map .flt) (fld ji "yp") (w "interp values")
  let cv : Values Float N := Values.ofFn fun i => co.get! i.1
  t.num (.approx 1e-8) (.flt (Forms.approx 0.75 cv)) (fld c "approx") (w "approx")

/-- Run the suite. -/
def suite : IO Tally := do
  let jr ← load "roots2"
  let t := (cases jr).toList.zipIdx.foldl (fun t (c, k) => rootsCase t c k) (Tally.new "forms/parity")
  let ex := fld jr "extra"
  let t := t.num .bits (.flt (Forms.rootsConst 2)) (fld ex "roots_const") fun _ => "roots(2.0)"
  let t := t.num .bits (.flt (Forms.rootsConst 2)) (fld ex "rootsreal_const") fun _ => "rootsreal(2.0)"
  let z1 := Forms.monicrootsC1 ⟨1, 2⟩
  let t := t.num .bits (.cpx z1.re z1.im) (fld ex "monicroots_c1") fun _ => "monicroots(1+2im)"
  let t := t.num .bits (.cpx z1.re z1.im) (fld ex "monicrootscomplex_c1") fun _ => "monicrootscomplex(1+2im)"
  let t := (arr (fld ex "complex_quadratic")).toList.zipIdx.foldl (fun t (c, k) =>
    let r := Forms.monicrootscomplexC (cplx (fld c "a0")) (flt1 (fld c "a1"))
    t.nums .bits (vals r) (fld c "roots") fun _ => s!"complex quadratic {k}") t
  let je ← load "eigvecs"
  let t := (cases je).toList.zipIdx.foldl (fun t (c, k) => eigCase t c k) t
  let jv ← load "vandermonde"
  let t := (arr (fld jv "ops")).toList.zipIdx.foldl (fun t (c, k) => vandOp t c k) t
  let t := (arr (fld jv "fits")).toList.zipIdx.foldl (fun t (c, k) => fitCase t c k) t
  -- Julia `vandermondereal(Endomorphism([2 1 0; 1 3 1; 0 1 4]))` and
  -- `vandermondecomplex(Endomorphism([0 -1; 1 0]))` (Grassmann 0.8.46)
  let A : Endomorphism (En 3) (.chain 1) Float := endo (En 3) [[2, 1, 0], [1, 3, 1], [0, 1, 4]]
  let t := match A.vandermondereal with
    | .ok M =>
      let want : List (List Float) := [[1.0, 1.267949192431123, 1.607695154586737], [1.0, 3.0, 9.0],
        [1.0, 4.732050807568878, 22.392304845413268]]
      t.ok ((M.toRows.zip want).all fun (r, w) => (r.zip w).all fun (x, y) => close 1e-13 x y) fun _ =>
        s!"vandermondereal = {M.toRows}"
    | .error e => t.ok false fun _ => s!"vandermondereal: {e}"
  let R : Endomorphism (En 2) (.chain 1) Float := endo (En 2) [[0, -1], [1, 0]]
  let C := R.vandermondecomplex
  let rows := C.toRows.map (·.map fun z => (z.re, z.im))
  let t := t.ok (rows.length == 2 && (rows.zip [[(1.0, 0.0), (0.0, -1.0)], [(1.0, 0.0), (0.0, 1.0)]]).all fun (r, w) =>
      (r.zip w).all fun ((a, b), (c, d)) => close 1e-14 a c && close 1e-14 b d) fun _ =>
    s!"vandermondecomplex = {rows}"
  return t

end Tests.FormsTests.Parity
