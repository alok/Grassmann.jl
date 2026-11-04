import Tests.Adapode.Common
import Adapode.Chebyshev

/-!
# Chebyshev collocation (`Adapode.Chebyshev`)

Reference values are Trefethen's programs (*Spectral Methods in MATLAB*) recomputed in NumPy/SciPy
with `cheb(N)` and `scipy.linalg.eig`, independent of the Julia code whose odd derivatives have the
wrong sign (B17): the clamped-beam eigenvalues of p38 (`N = 16`: 31.28524386, 237.72106753; the
exact first value is `(4.7300407448627/2)⁴ = 31.2852…`), the most unstable Orr–Sommerfeld mode at
`R = 5772` (p40, `N = 60`: `−7.819155e−5 − 0.26156767i`), `u(0)` for `u″ = eᵘ` (p14, `N = 16`:
`−0.36805602444148605` after 29 iterations) and the disk eigenvalues `j₀₁² = 5.783186`,
`j₁₁² = 14.681971` (p28). Polynomial identities are exact: the biharmonic maps `(1 − x²)²` to 24,
the polar Laplacian maps `1 − r²` to `−4`, and the 2-D Helmholtz and biharmonic operators are exact
on products of such polynomials.
-/

open Lean Tests.Small Cartan Cartan.Spectral Cartan.Solve Adapode.Chebyshev

namespace Tests.AdapodeTests.Chebyshev

/-- `|a − b| ≤ tol·max(1, |b|)`. -/
def near (a b : Float) (tol : Float := 1e-10) : Bool := (a - b).abs ≤ tol * max 1 b.abs

/-- `max |a − b|`. -/
def maxDiff (a b : FloatArray) : Float :=
  (List.range a.size).foldl (fun m i => max m (a.get! i - b.get! i).abs) (if a.size == b.size then 0 else 1e300)

/-- Values on the column-major grid `x × y`. -/
def grid2 (x y : FloatArray) (f : Float → Float → Float) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity (x.size * y.size)
  for j in [0:y.size] do
    for i in [0:x.size] do
      out := out.push (f (x.get! i) (y.get! j))
  return out

/-- Operators applied to exact polynomials. -/
def identities : TestM Unit := do
  let x := chebyshevPoints 17
  let int := fun (f : Float → Float) => (⟨(Array.range 15).map fun i => f (x.get! (i + 1))⟩ : FloatArray)
  let b := (biharmonic1 x).mulVec (int fun v => (1 - v ^ 2) ^ 2)
  check "chebyshev: biharmonic maps (1−x²)² to 24 (B17)" (maxDiff b (int fun _ => 24) < 1e-9)
    fun _ => s!"{b.data}"
  let h := (helmholtz1 x 3).mulVec (int fun v => (1 - v ^ 2) * v ^ 3)
  let e := maxDiff h (int fun v => 6 * v - 20 * v ^ 3 + 9 * (1 - v ^ 2) * v ^ 3)
  check "chebyshev: helmholtz(k = 3) is u″ + 9u" (e < 1e-10) fun _ => s!"{e}"
  let s := solveHelmholtz1 x ⟨x.data.map fun v => 6 * v - 20 * v ^ 3⟩
  let e := maxDiff s ⟨x.data.map fun v => (1 - v ^ 2) * v ^ 3⟩
  check "chebyshev: solvehelmholtz recovers (1−x²)x³ with zero ends" (e < 1e-13) fun _ => s!"{e}"
  -- 2-D on Chebyshev(13) × Chebyshev(11)
  let y := chebyshevPoints 11
  let x2 := chebyshevPoints 13
  let u := grid2 x2 y fun a b => (1 - a ^ 2) * (1 - b ^ 2) * (a + 2 * b)
  let lap := grid2 x2 y fun a b => (1 - b ^ 2) * (-6 * a - 4 * b) + (1 - a ^ 2) * (-2 * a - 12 * b)
  let e := maxDiff (solveHelmholtz2 x2 y lap) u
  check "chebyshev: 2-D solvehelmholtz recovers (1−x²)(1−y²)(x+2y)" (e < 1e-12) fun _ => s!"{e}"
  let w := grid2 x2 y fun a b => (1 - a ^ 2) ^ 2 * (1 - b ^ 2) ^ 2
  let bw := (biharmonic2 x2 y).mulVec (interior #[13, 11] w)
  let exact := interior #[13, 11] (grid2 x2 y fun a b =>
    24 * (1 - b ^ 2) ^ 2 + 2 * (12 * a ^ 2 - 4) * (12 * b ^ 2 - 4) + 24 * (1 - a ^ 2) ^ 2)
  let e := maxDiff bw exact
  check "chebyshev: 2-D biharmonic is ∇⁴ on (1−x²)²(1−y²)²" (e < 1e-8) fun _ => s!"{e}"
  let L := polarLaplacian 13 21
  let r := polarRadii 13
  let v : FloatArray := ⟨(Array.range (12 * 20)).map fun q => 1 - r.get! (q % 12 + 1) ^ 2⟩
  let e := maxDiff (L.mulVec v) ⟨Array.replicate 240 (-4)⟩
  check "chebyshev: polar Laplacian maps 1 − r² to −4 (B17)" (e < 1e-10) fun _ => s!"{e}"
  let v2 : FloatArray := ⟨(Array.range (12 * 20)).map fun q =>
    let ρ := r.get! (q % 12 + 1)
    let θ := 2 * 3.141592653589793 * (q / 12 + 1).toFloat / 20
    (1 - ρ ^ 2) * ρ ^ 3 * Float.cos (3 * θ)⟩
  let w2 : FloatArray := ⟨(Array.range (12 * 20)).map fun q =>
    let ρ := r.get! (q % 12 + 1)
    let θ := 2 * 3.141592653589793 * (q / 12 + 1).toFloat / 20
    ρ ^ 3 * Float.cos (3 * θ) * (-16)⟩
  let e := maxDiff (L.mulVec v2) w2
  check "chebyshev: polar Laplacian of (1 − r²)r³ cos 3θ is −16 r³ cos 3θ" (e < 1e-9) fun _ => s!"{e}"
  -- solvepolardirichlet(L, f) with f = −4: (1 − r²)/max
  let f : FloatArray := ⟨Array.replicate (13 * 21) (-4)⟩
  let sp := solvePolarDirichlet L 13 21 f
  let m := 1 - r.get! 12 ^ 2
  let ok := (List.range 13).all fun i => (List.range 21).all fun j =>
    near (sp.get! (j * 13 + i)) (if i == 0 then 0 else (1 - r.get! i ^ 2) / m) 1e-12
  check "chebyshev: solvepolardirichlet of −4 is (1 − r²)/‖·‖∞" ok fun _ => s!"{sp.data.extract 0 13}"

/-- Eigenvalues and the nonlinear iteration against Trefethen's programs. -/
def trefethen : TestM Unit := do
  let B := biharmonic1 (chebyshevPoints 17)
  let l1 := eigNearReal B 30
  let l2 := eigNearReal B 240
  check "chebyshev: clamped beam λ₁ (p38)" (near l1 31.28524386 1e-9) fun _ => s!"{l1}"
  check "chebyshev: clamped beam λ₂ (p38)" (near l2 237.72106753 1e-9) fun _ => s!"{l2}"
  let (A, Bm) := orrSommerfeld (chebyshevPoints 61)
  let ((lr, li), _) := eigNear A Bm (0, -0.26)
  check "chebyshev: Orr–Sommerfeld critical mode at R = 5772 (p40)"
    ((lr - (-7.819155296635369e-05)).abs < 1e-9 && (li - (-0.2615676703047179)).abs < 1e-9)
    fun _ => s!"{lr} {li}"
  let (u, it) := solveNonlinearHelmholtz1 Float.exp 0 17
  check "chebyshev: u″ = eᵘ, u(0) (p14)" (near (u.get! 8) (-0.36805602444148605) 1e-13 && it == 29)
    fun _ => s!"{u.get! 8} after {it}"
  let L := polarLaplacian 13 21
  let d1 := eigNearReal L (-5)
  let d2 := eigNearReal L (-15)
  check "chebyshev: disk eigenvalue −j₀₁² (p28)" (near d1 (-5.783185962946784) 1e-9) fun _ => s!"{d1}"
  check "chebyshev: disk eigenvalue −j₁₁² (p28)" (near d2 (-14.681970642123893) 1e-8) fun _ => s!"{d2}"
  let (u2, _) := solveNonlinearHelmholtz2 (fun v => 1 + v ^ 2 / 4) 1 9 9
  let L2 := helmholtz2 (chebyshevPoints 9) (chebyshevPoints 9) 1
  let res := maxDiff (L2.mulVec (interior #[9, 9] u2)) (interior #[9, 9] ⟨u2.data.map fun v => 1 + v ^ 2 / 4⟩)
  check "chebyshev: 2-D nonlinear Helmholtz converges to a solution" (res < 1e-13) fun _ => s!"{res}"

/-- Run the Chebyshev checks. -/
def run : TestM Unit := do
  identities
  trefethen

end Tests.AdapodeTests.Chebyshev
