import Cartan.Spectral
import Adapode.Grid

/-!
# Chebyshev collocation operators (Adapode.jl `src/grid.jl:50-212`)

Port notes: `docs/port-notes/adapode.md` §2.7. Spectral collocation on Chebyshev–Lobatto points
(Trefethen, *Spectral Methods in MATLAB*): the Dirichlet Helmholtz operator `D²[int,int] + k²I` in
one and two dimensions (programs 13, 16), the Picard iteration for `u″ = f(u)` (p14), the clamped
biharmonic operator (p38), the Orr–Sommerfeld pencil (p40) and the polar Laplacian on the disk
(p28). Grids are column-major with axis 1 fastest; operators act on the interior unknowns in that
order (`kron(I, D2X) + kron(D2Y, I)`).

Eigenvalues of the (non-symmetric) operators come from shifted inverse iteration on the complex
pencil `(A − σB)⁻¹B`, solved in the real `2n × 2n` form `[Cᵣ −Cᵢ; Cᵢ Cᵣ]`.

**Julia defects fixed** (`oracle/adapode/defects.toml`):
* **B17** `biharmonic`, `orrsommerfeld` and `polarlaplacian` build on Cartan's `ChebyshevMatrix`,
  which differentiates the descending nodes (`−d/dx` on Julia's ascending points), so the odd
  derivatives (`−8x D³`, the `(1/r)∂_r` term) change sign: here `D` is `d/dx` on the nodes used;
* **B19** `solvenonlinearhelmholtz` calls the undefined `nonlinearhelmholtz`: here it runs the
  Picard iteration from zero;
* `solveiteration` has no iteration cap: here `fuel` bounds it and the count is returned.
-/

namespace Adapode.Chebyshev

open Cartan Cartan.Spectral Cartan.Solve JuliaBase

/-! ## Dense helpers -/

/-- Julia `kron(A, B)`: block `(i, j)` is `A[i,j]·B`. -/
def kron (A B : Dense) : Dense :=
  Dense.ofFn (A.rows * B.rows) (A.cols * B.cols) fun p q =>
    A.get (p / B.rows) (q / B.cols) * B.get (p % B.rows) (q % B.cols)

/-- The square block `A[lo:hi, lo:hi]` (0-based, `hi` exclusive). -/
def block (A : Dense) (lo hi : Nat) : Dense :=
  Dense.ofFn (hi - lo) (hi - lo) fun i j => A.get (lo + i) (lo + j)

/-- A diagonal matrix. -/
def diag (d : FloatArray) : Dense :=
  Dense.ofFn d.size d.size fun i j => if i == j then d.get! i else 0

/-- `A + s·I`. -/
def addId (A : Dense) (s : Float) : Dense :=
  Dense.ofFn A.rows A.cols fun i j => A.get i j + (if i == j then s else 0)

/-- `A − B`. -/
def sub (A B : Dense) : Dense := Dense.add A (Dense.scale (-1) B)

/-! ## Interior unknowns and zero boundary padding (`grid.jl:54-139`) -/

/-- The interior points of a column-major grid (every index in `1 … n−2`), in order. -/
def interiorIndices (dims : Array Nat) : Array Nat := Id.run do
  let total := dims.foldl (· * ·) 1
  let mut out := #[]
  for q in [0:total] do
    let mut r := q
    let mut inside := true
    for n in dims do
      let i := r % n
      if i == 0 || i + 1 == n then inside := false
      r := r / n
    if inside then out := out.push q
  return out

/-- Julia `vec(f[2:N−1, 2:M−1, …])`. -/
def interior (dims : Array Nat) (f : FloatArray) : FloatArray :=
  ⟨(interiorIndices dims).map f.get!⟩

/-- Julia `reshapedirichlet(f, u)`: the interior values `u` padded with zeros. -/
def reshapeDirichlet (dims : Array Nat) (u : FloatArray) : FloatArray := Id.run do
  let mut out : FloatArray := ⟨Array.replicate (dims.foldl (· * ·) 1) 0⟩
  let idx := interiorIndices dims
  for k in [0:idx.size] do
    out := out.set! idx[k]! (u.get! k)
  return out

/-- Julia `solvedirichlet(L, f)`: `L \ f[interior]`, padded with the zero boundary. -/
def solveDirichlet (L : Dense) (dims : Array Nat) (f : FloatArray) : FloatArray :=
  reshapeDirichlet dims (Dense.solve L (interior dims f))

/-- Julia `dirichlet!(u)`: zero every boundary hyperface. -/
def dirichletZero (dims : Array Nat) (u : FloatArray) : FloatArray :=
  reshapeDirichlet dims (interior dims u)

/-! ## Helmholtz (`grid.jl:151-175`) -/

/-- The second-derivative matrix on the points `x` (`D²`, `D` the Chebyshev matrix on `x`). -/
def secondDerivative (x : FloatArray) : Dense :=
  let D := chebyshevMatrixOn x
  Dense.mul D D

/-- Julia `helmholtz(f::AbstractVector, k)`: `D²[2:N−1, 2:N−1] + k²I` on the points `x`. -/
def helmholtz1 (x : FloatArray) (k : Float := 0) : Dense :=
  addId (block (secondDerivative x) 1 (x.size - 1)) (k * k)

/-- Julia `helmholtz(f::AbstractMatrix, k)`: `kron(I, D2X) + kron(D2Y, I) + k²I` on the grid
`x × y`. -/
def helmholtz2 (x y : FloatArray) (k : Float := 0) : Dense :=
  let D2X := block (secondDerivative x) 1 (x.size - 1)
  let D2Y := block (secondDerivative y) 1 (y.size - 1)
  addId (Dense.add (kron (Dense.identity D2Y.rows) D2X) (kron D2Y (Dense.identity D2X.rows))) (k * k)

/-- Julia `solvehelmholtz(f, k)` in 1-D: `u″ + k²u = f`, `u(±1) = 0`. -/
def solveHelmholtz1 (x f : FloatArray) (k : Float := 0) : FloatArray :=
  solveDirichlet (helmholtz1 x k) #[x.size] f

/-- Julia `solvehelmholtz(f, k)` in 2-D: `Δu + k²u = f`, `u = 0` on the boundary. -/
def solveHelmholtz2 (x y f : FloatArray) (k : Float := 0) : FloatArray :=
  solveDirichlet (helmholtz2 x y k) #[x.size, y.size] f

/-- Julia `solveiteration(L, f, u, solvedirichlet)`: the Picard iteration
`u ← solvedirichlet(L, f.(u))` until `‖Δu‖∞ ≤ 5ε`, at most `fuel` times. Returns the iterate and
the number of iterations. -/
def solveIteration (L : Dense) (dims : Array Nat) (f : Float → Float) (u : FloatArray)
    (fuel : Nat := 1000) : FloatArray × Nat :=
  go fuel u 0
where
  go : Nat → FloatArray → Nat → FloatArray × Nat
    | 0, u, n => (u, n)
    | fuel + 1, u, n =>
      let unew := solveDirichlet L dims ⟨u.data.map f⟩
      let change := (List.range u.size).foldl (fun m i => max m (unew.get! i - u.get! i).abs) 0
      if change ≤ 5 * 2.220446049250313e-16 then (unew, n + 1) else go fuel unew (n + 1)

/-- Julia `solvenonlinearhelmholtz(f, k, N)` (B19: calls an undefined function): the Picard
iteration for `u″ + k²u = f(u)`, `u(±1) = 0`, from `u = 0` on `Chebyshev(N)`. -/
def solveNonlinearHelmholtz1 (f : Float → Float) (k : Float) (N : Nat) (fuel : Nat := 1000) :
    FloatArray × Nat :=
  solveIteration (helmholtz1 (chebyshevPoints N) k) #[N] f ⟨Array.replicate N 0⟩ fuel

/-- Julia `solvenonlinearhelmholtz(f, k, N, M)` on `Chebyshev(N) × Chebyshev(M)`. -/
def solveNonlinearHelmholtz2 (f : Float → Float) (k : Float) (N M : Nat) (fuel : Nat := 1000) :
    FloatArray × Nat :=
  solveIteration (helmholtz2 (chebyshevPoints N) (chebyshevPoints M) k) #[N, M] f
    ⟨Array.replicate (N * M) 0⟩ fuel

/-! ## Biharmonic and Orr–Sommerfeld (`grid.jl:187-212`) -/

/-- Julia `biharmonic(v)` (Trefethen p38, B17 fixed): the clamped fourth derivative
`((1−x²)D⁴ − 8xD³ − 12D²)·S` on the interior, `S = diag(0, 1/(1−x²), 0)`; it maps the values of
`u = (1−x²)p` to `u⁗` for `p` vanishing at `±1`. -/
def biharmonic1 (x : FloatArray) : Dense :=
  let N := x.size
  let D := chebyshevMatrixOn x
  let D2 := Dense.mul D D
  let D3 := Dense.mul D2 D
  let D4 := Dense.mul D3 D
  let S := diag ⟨(Array.range N).map fun i =>
    if i == 0 || i + 1 == N then 0 else 1 / (1 - x.get! i ^ 2)⟩
  let P := sub (sub (Dense.mul (diag ⟨x.data.map fun v => 1 - v ^ 2⟩) D4)
    (Dense.scale 8 (Dense.mul (diag x) D3))) (Dense.scale 12 D2)
  block (Dense.mul P S) 1 (N - 1)

/-- Julia `biharmonic(v::AbstractMatrix)`: `∇⁴ = D4X ⊕ D4Y + 2·D2Y ⊗ D2X` on `x × y`. -/
def biharmonic2 (x y : FloatArray) : Dense :=
  let D2X := block (secondDerivative x) 1 (x.size - 1)
  let D2Y := block (secondDerivative y) 1 (y.size - 1)
  let IX := Dense.identity D2X.rows
  let IY := Dense.identity D2Y.rows
  Dense.add (Dense.add (kron IY (biharmonic1 x)) (kron (biharmonic1 y) IX))
    (Dense.scale 2 (Dense.mul (kron D2Y IX) (kron IY D2X)))

/-- A complex dense matrix `re + i·im`. -/
structure CDense where
  /-- The real part. -/
  re : Dense
  /-- The imaginary part. -/
  im : Dense
  deriving Inhabited

/-- Julia `orrsommerfeld(v, R)` (Trefethen p40, B17 fixed): the pencil `A u = λ B u` with
`A = (D⁴ − 2D² + I)/R − 2iI − i·diag(1 − x²)(D² − I)` and `B = D² − I` on the interior points. -/
def orrSommerfeld (x : FloatArray) (R : Float := 5772) : CDense × Dense :=
  let N := x.size
  let n := N - 2
  let D2 := block (secondDerivative x) 1 (N - 1)
  let D4 := biharmonic1 x
  let Iₙ := Dense.identity n
  let B := addId D2 (-1)
  let Ar := Dense.scale (1 / R) (addId (Dense.add D4 (Dense.scale (-2) D2)) 1)
  let U := diag ⟨(Array.range n).map fun i => 1 - x.get! (i + 1) ^ 2⟩
  let Ai := Dense.add (Dense.scale (-2) Iₙ) (Dense.scale (-1) (Dense.mul U B))
  (⟨Ar, Ai⟩, B)

/-! ## The polar Laplacian (`grid.jl:177-185`, Trefethen p28) -/

/-- The radial nodes of `polarlaplacian(N, M)`: `cos(jπ/(2N−1))`, `j = 0 … 2N−1` (descending, so
`r[1] = 1` is the boundary and `r[2:N]` are the positive interior radii). -/
def polarRadii (N : Nat) : FloatArray :=
  ⟨(Array.range (2 * N)).map fun j => (cossinpiRat j (2 * N - 1)).1⟩

/-- Julia `polarlaplacian(N, M)` (B17 fixed): the Laplacian on the unit disk for the unknowns at
the radii `r[2:N]` (fastest) and the `M − 1` angles `2πj/(M−1)`, `M − 1` even:
`kron(I, D1 + R E1) + kron([0 I; I 0], D2 + R E2) + kron(D2θ, R²)`. -/
def polarLaplacian (N : Nat := 13) (M : Nat := 21) : Dense :=
  let r := polarRadii N
  let D := chebyshevMatrixOn r
  let DD := Dense.mul D D
  let n := N - 1
  let mirror := fun (j : Nat) => 2 * N - 2 - j  -- 0-based column 2N−1−(j+1)
  let D1 := Dense.ofFn n n fun i j => DD.get (i + 1) (j + 1)
  let D2 := Dense.ofFn n n fun i j => DD.get (i + 1) (mirror j)
  let E1 := Dense.ofFn n n fun i j => D.get (i + 1) (j + 1)
  let E2 := Dense.ofFn n n fun i j => D.get (i + 1) (mirror j)
  let Rv : FloatArray := ⟨(Array.range n).map fun i => 1 / r.get! (i + 1)⟩
  let Rm := diag Rv
  let D2t := derivetoeplitz2 (M - 1)
  let M2 := (M - 1) / 2
  let swap := Dense.ofFn (M - 1) (M - 1) fun i j => if j == (i + M2) % (2 * M2) then 1 else 0
  Dense.add (Dense.add (kron (Dense.identity (M - 1)) (Dense.add D1 (Dense.mul Rm E1)))
    (kron swap (Dense.add D2 (Dense.mul Rm E2)))) (kron D2t (diag ⟨Rv.data.map (· ^ 2)⟩))

/-- Julia `reshapepolardirichlet(f, u)`: the `N × M` grid with the boundary row `0` and the
`(N−1) × (M−1)` unknowns, the last angle repeated first (`[:, vcat(M−1, 1:M−1)]`). -/
def reshapePolarDirichlet (N M : Nat) (u : FloatArray) : FloatArray :=
  Dense.data <| Dense.ofFn N M fun i j =>
    if i == 0 then 0 else
      let c := if j == 0 then M - 2 else j - 1
      u.get! (c * (N - 1) + (i - 1))

/-- Julia `solvepolardirichlet(L, f)`: `L \ vec(f[2:N, 2:M])`, reshaped by
`reshapePolarDirichlet` and divided by its `∞`-norm (as Julia does). -/
def solvePolarDirichlet (L : Dense) (N M : Nat) (f : FloatArray) : FloatArray :=
  let rhs : FloatArray := ⟨(Array.range ((N - 1) * (M - 1))).map fun q =>
    f.get! ((q / (N - 1) + 1) * N + (q % (N - 1) + 1))⟩
  let u := reshapePolarDirichlet N M (Dense.solve L rhs)
  let m := u.data.foldl (fun m v => max m v.abs) 0
  ⟨u.data.map (· / m)⟩

/-! ## Eigenvalues by shifted inverse iteration -/

/-- The real `2n × 2n` form `[Cᵣ −Cᵢ; Cᵢ Cᵣ]` of a complex matrix. -/
def realForm (C : CDense) : Dense :=
  let n := C.re.rows
  Dense.ofFn (2 * n) (2 * n) fun i j =>
    let (a, b) := (i % n, j % n)
    if (i < n) == (j < n) then C.re.get a b
    else if i < n then -(C.im.get a b) else C.im.get a b

/-- The eigenvalue of the pencil `A u = λ B u` nearest the shift `σ` and its eigenvector
(interleaved `(re, im)`), by inverse iteration with `(A − σB)⁻¹B`; stops when `λ` changes by at
most `tol·|λ|`. -/
def eigNear (A : CDense) (B : Dense) (σ : Float × Float) (tol : Float := 1e-13)
    (fuel : Nat := 500) : (Float × Float) × FloatArray :=
  let n := B.rows
  let C : CDense := ⟨sub A.re (Dense.scale σ.1 B), Dense.add A.im (Dense.scale (-σ.2) B)⟩
  let F := Dense.lu (realForm C)
  let x0 : FloatArray := ⟨(Array.range (2 * n)).map fun i =>
    if i < n then 1 + 0.1 * Float.sin (i.toFloat) else 0.1 * Float.cos (i.toFloat)⟩
  go F n fuel x0 (0, 0)
where
  go (F : Dense.LU) (n : Nat) : Nat → FloatArray → Float × Float → (Float × Float) × FloatArray
    | 0, x, lam => (lam, x)
    | fuel + 1, x, lam =>
      let xr : FloatArray := ⟨x.data.extract 0 n⟩
      let xi : FloatArray := ⟨x.data.extract n (2 * n)⟩
      let y := F.solve ⟨(Dense.mulVec B xr).data ++ (Dense.mulVec B xi).data⟩
      -- μ = xᴴy / xᴴx, λ = σ + 1/μ
      let (pr, pi, nx) := (List.range n).foldl (fun (pr, pi, nx) k =>
        let (ar, ai, br, bi) := (x.get! k, x.get! (n + k), y.get! k, y.get! (n + k))
        (pr + ar * br + ai * bi, pi + ar * bi - ai * br, nx + ar * ar + ai * ai)) (0, 0, 0)
      let (mr, mi) := (pr / nx, pi / nx)
      let d := mr * mr + mi * mi
      let new := (σ.1 + mr / d, σ.2 - mi / d)
      let ny := Float.sqrt ((List.range (2 * n)).foldl (fun s k => s + y.get! k ^ 2) 0)
      let x' : FloatArray := ⟨y.data.map (· / ny)⟩
      let δ := Float.sqrt ((new.1 - lam.1) ^ 2 + (new.2 - lam.2) ^ 2)
      if δ ≤ tol * Float.sqrt (new.1 ^ 2 + new.2 ^ 2) then (new, x') else go F n fuel x' new

/-- The eigenvalue of a real matrix nearest the real shift `σ`. -/
def eigNearReal (A : Dense) (σ : Float) (tol : Float := 1e-13) : Float :=
  (eigNear ⟨A, Dense.zeros A.rows A.cols⟩ (Dense.identity A.rows) (σ, 0) tol).1.1

end Adapode.Chebyshev
