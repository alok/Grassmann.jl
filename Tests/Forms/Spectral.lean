import Tests.Forms.Common

/-!
# Eigen-decompositions, matrix logarithms and polynomial roots against Julia

* `eigen.json`: Julia's `eigen(Endomorphism(A))` (LAPACK). Eigenvalues within
  `rtol = 1e-9` (as multisets when LAPACK's `(re, im)` order is decided by rounding
  noise), the real/complex type, `tr`; eigenvectors by their residual
  `‖A v − λ v‖ ≤ 1e-9 · max(1, ‖A‖)` and unit norm (LAPACK leaves the sign/phase free).
* `log.json`: Julia `log(Endomorphism(A))` of symmetric positive definite matrices
  (`log(::Symmetric)`, eigen-based), `rtol = 1e-12`.
* `roots.json`: `monicroots`, `monicrootsreal` (with Julia's `DomainError`s) and
  `monicrootscomplex` of degree 1-4: the real/complex result type exactly, values bit
  for bit except through `acos`/`cos` (the Viète branch, and the quartic's resolvent):
  `rtol = 1e-12`.
-/

namespace Tests.FormsTests.SpectralSuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- The eigen-decomposition checks of one case. -/
def eigenCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let rowsA := floatRows (fld c "A")
  let n := rowsA.length
  let V := En n
  let A : Endomorphism V (.chain 1) Float := endo V rowsA
  let w := fun (s : String) => fun (_ : Unit) => s!"eigen case {k} (n={n}) {s}"
  let mut t := t
  let d := A.eigenDecomposition
  let juliaReal := (fld c "real") == .bool true
  t := t.ok (d.real == juliaReal) (w s!"real-typed: Lean {d.real}, Julia {juliaReal}")
  let lams : List Num := (List.range n).map fun i =>
    if d.real then .flt (d.re.get! i) else .cpx (d.re.get! i) (d.im.get! i)
  t := t.numsSet (.approx 1e-9) lams (fld c "vals") (w "eigenvalues")
  -- residuals and norms
  let normA := (List.range (n * n)).foldl (fun m i => max m (A.entry (i / n) (i % n)).abs) 1
  for j in [0:n] do
    let lr := d.re.get! j
    let li := d.im.get! j
    let mut res : Float := 0
    let mut nrm : Float := 0
    for i in [0:n] do
      let vr := d.vre.get! (i * n + j)
      let vi := d.vim.get! (i * n + j)
      nrm := nrm + vr * vr + vi * vi
      let (sr, si) := (List.range n).foldl (fun (sr, si) k =>
        (sr + A.entry i k * d.vre.get! (k * n + j), si + A.entry i k * d.vim.get! (k * n + j))) ((0 : Float), (0 : Float))
      let er := sr - (lr * vr - li * vi)
      let ei := si - (lr * vi + li * vr)
      res := max res (Float.sqrt (er * er + ei * ei))
    t := t.ok (res ≤ 1e-9 * normA) (w s!"residual of eigenvector {j}: {res}")
    t := t.ok ((nrm - 1).abs ≤ 1e-12) (w s!"norm of eigenvector {j}: {nrm}")
  match fld c "tr" with
  | .null => pure ()
  | tr =>
    match A.eigen with
    | .real S => t := t.num (.approx 1e-12) (.flt S.tr) tr (w "tr")
    | .complex S => t := t.num (.approx 1e-12) (.cpx S.tr.re S.tr.im) tr (w "tr")
  return t

/-- One matrix logarithm case. -/
def logCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  let rowsA := floatRows (fld c "A")
  let n := rowsA.length
  let V := En n
  let A : Endomorphism V (.chain 1) Float := endo V rowsA
  match A.log with
  | .ok L => t.mat (.approx 1e-12) (opRows L) (fld c "log") fun _ => s!"log case {k}"
  | .error e => t.ok false fun _ => s!"log case {k}: {e}"

/-- Julia's roots golden: a scalar for degree 1 (a real, or a `[re, im]` pair for
`monicrootscomplex`), else a list of reals or of pairs (Julia's result type). -/
def rootsEq {n : Nat} (t : Tally) (m : Mode) (s : Forms.Spectrum n) (want : Json) (what : Unit → String) :
    Tally :=
  if (jerr? want).isSome then t.skip
  else if n == 1 then
    let z := s.toList.headD ⟨0, 0⟩
    match want with
    | .arr _ => t.num m (.cpx z.re z.im) want what
    | _ => t.num m (.flt z.re) want what
  else
    let juliaComplex := match (arr want)[0]? with | some (.arr _) => true | _ => false
    let t := t.ok (juliaComplex == !s.isReal) fun _ => s!"{what ()}: result type (Lean real = {s.isReal})"
    match s with
    | .real v => t.nums m (vals v) want what
    | .complex v => t.nums m (vals v) want what

/-- One polynomial-roots case. -/
def rootsCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let a := flts (fld c "a")
  let n := a.length
  let av : Values Float n := Values.ofFn fun i => a[i.1]!
  let w := fun (s : String) => fun (_ : Unit) => s!"roots case {k} a={a} {s}"
  let m : Mode := .approx 1e-12
  let mut t := t
  match Forms.Roots.monicroots? av with
  | some s => t := rootsEq t m s (fld c "roots") (w "monicroots")
  | none => t := t.ok false (w "degree")
  match Forms.Roots.monicrootsreal? av with
  | some (.ok v) => t := rootsEq t m (.real v) (fld c "real") (w "monicrootsreal")
  | some (.error e) => t := t.ok ((jerr? (fld c "real")).isSome) (w s!"monicrootsreal: Lean {e}, Julia {(fld c "real").compress}")
  | none => t := t.ok false (w "degree")
  match Forms.Roots.monicrootscomplex? av with
  | some v => t := rootsEq t m (.complex v) (fld c "complex") (w "monicrootscomplex")
  | none => t := t.ok false (w "degree")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let je ← load "eigen"
  let t := (cases je).toList.zipIdx.foldl (fun t (c, k) => eigenCase t c k) (Tally.new "forms/spectral")
  let jl ← load "log"
  let t := (cases jl).toList.zipIdx.foldl (fun t (c, k) => logCase t c k) t
  let jr ← load "roots"
  let t := (cases jr).toList.zipIdx.foldl (fun t (c, k) => rootsCase t c k) t
  -- the quartic factorisation and the resolvent's largest root
  let ex := fld jr "extra"
  let (q1, q2, p1, p2) := Forms.Roots.quartic 1 2 3 4
  let t := t.nums (.approx 1e-12) (ns [q1, q2, p1, p2]) (fld ex "quartic1234") fun _ => "quartic(1,2,3,4)"
  let t := t.num .bits (.flt (Forms.Roots.cubicmax 2 3 1)) (fld ex "cubicmax231") fun _ => "cubicmax(2,3,1)"
  return t

end Tests.FormsTests.SpectralSuite
