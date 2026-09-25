/-
Polynomial least-squares fits through Vandermonde matrices (Grassmann.jl
`src/composite.jl:856-885`): `polynom`, `approx`, the rectangular `vandermonde(x, N)`,
the fit `vandermonde(x, y, N)` and `vandermondeinterp(x, y, N, grid)`.

Julia's working methods take `Array`s: `vandermonde(x, N)` is the `m × N` matrix
`[xᵢ^d]` (`composite.jl:863-869`) and `vandermonde(x, y, N) = vandermonde(x, N) \ y`
solves the least-squares problem with LAPACK's pivoted QR (a square system with LU).
Here the solve is a Householder QR (`lstsq`), so the coefficients agree with Julia to
rounding (`rtol ≈ 1e-12` on well-conditioned fits), not bit for bit.

Julia defect fixed rather than replicated: the `Values`/`Chain` method
`vandermonde(x, y, V)` (`composite.jl:871`) applies `\` to a `Values` right-hand side
entry by entry, returning a `Values` of scaled pseudo-inverses instead of the coefficients
(so `vandermondeinterp` of `Values` inputs is broken too); `vandermondeFit` gives the
coefficients for every input.
-/
import Grassmann.Forms.Spectral
import JuliaBase.Range

namespace Grassmann.Forms

open StaticVectors JuliaBase

/-- Julia `polynom(x, Val(N))` (`composite.jl:875`): `(1, x, x², …, x^{N-1})`, each power
Julia's literal power (`x*x`, `x*x*x`, then `x^k`). -/
@[inline] def polynom (x : Float) (N : Nat) : Values Float N :=
  Values.ofFn fun i => F64.literalPow x i.1

/-- The loop of `approx`: `Σ_{i ≥ k} cᵢ xⁱ` added to `acc` in index order. -/
def approxLoop {N : Nat} (x : Float) (c : Values Float N) (k : Nat) (acc : Float) : Float :=
  if h : k < N then approxLoop x c (k + 1) (acc + F64.literalPow x k * c.get ⟨k, h⟩) else acc
termination_by N - k

/-- Julia `approx(x, y::Values{N})` (`composite.jl:859`): the polynomial with coefficients
`y` (constant term first) at `x`, `polynom(x) ⋅ y`. -/
@[inline] def approx {N : Nat} (x : Float) (c : Values Float N) : Float := approxLoop x c 0 0

/-- Julia `vandermonde(x::Array, N)` (`composite.jl:863-869`): the `m × N` matrix
`V[i, d] = xᵢ^d` (`d = 0 … N-1`, Julia's `x.^d`), row-major. -/
def vandermondeRows (x : FloatArray) (N : Nat) : FloatArray :=
  go 0 (FloatArray.emptyWithCapacity (x.size * N))
where
  /-- Fill row by row. -/
  go (t : Nat) (out : FloatArray) : FloatArray :=
    if t < x.size * N then go (t + 1) (out.push (F64.powInt (x.get! (t / N)) (t % N)))
    else out
  termination_by x.size * N - t

/-- Householder QR least squares of the row-major `m × n` matrix `A` (`m ≥ n`, full column
rank) against `b`: the `n` coefficients minimising `‖A c − b‖₂` (Julia `A \ b`). -/
def lstsq (A : FloatArray) (m n : Nat) (b : FloatArray) : FloatArray := Id.run do
  let mut a := A
  let mut y := b
  for k in [0:n] do
    -- the Householder vector of column k below the diagonal
    let mut s : Float := 0
    for i in [k:m] do
      let v := a.get! (i * n + k)
      s := s + v * v
    let nrm := s.sqrt
    if nrm != 0 then
      let akk := a.get! (k * n + k)
      let alpha := if akk > 0 then -nrm else nrm
      -- v = x − α e₁, stored in place; vᵀv = 2(nrm² − α·akk)
      a := a.set! (k * n + k) (akk - alpha)
      let vtv := 2 * (s - alpha * akk)
      -- apply H = I − 2vvᵀ/vᵀv to the remaining columns and to y
      for j in [k+1:n] do
        let mut d : Float := 0
        for i in [k:m] do d := d + a.get! (i * n + k) * a.get! (i * n + j)
        let f := 2 * d / vtv
        for i in [k:m] do a := a.set! (i * n + j) (a.get! (i * n + j) - f * a.get! (i * n + k))
      let mut d : Float := 0
      for i in [k:m] do d := d + a.get! (i * n + k) * y.get! i
      let f := 2 * d / vtv
      for i in [k:m] do y := y.set! i (y.get! i - f * a.get! (i * n + k))
      a := a.set! (k * n + k) alpha
  -- back substitution with R (the upper triangle)
  let mut c := FloatArray.mk (Array.replicate n 0)
  for kk in [0:n] do
    let k := n - 1 - kk
    let mut t := y.get! k
    for j in [k+1:n] do t := t - a.get! (k * n + j) * c.get! j
    c := c.set! k (t / a.get! (k * n + k))
  return c

/-- Julia `vandermonde(x, y, N)` (`composite.jl:862`, `Array` inputs): the coefficients
`(c₀, …, c_{N-1})` of the least-squares polynomial fit of the points `(xᵢ, yᵢ)`. -/
def vandermondeFit (x y : FloatArray) (N : Nat) : FloatArray :=
  lstsq (vandermondeRows x N) x.size N y

/-- The fit as `Values` (Julia `vandermonde(x, y, V)` with `N = mdims(V)`, whose `Values`
method is defective in Julia: module docstring). -/
@[inline] def vandermondeFitValues {m : Nat} (x y : Values Float m) (N : Nat) : Values Float N :=
  let c := vandermondeFit x.data y.data N
  Values.ofFn fun i => c.get! i.1

/-- The loop of `vandermondeinterp`: `yp += c_d · xp.^d` for `d = 1 … N-1`. -/
def interpLoop (c xp : FloatArray) (d : Nat) (yp : FloatArray) : FloatArray :=
  if d < c.size then
    let cd := c.get! d
    interpLoop c xp (d + 1)
      (FloatArray.mk ((Array.range xp.size).map fun i => yp.get! i + cd * F64.powInt (xp.get! i) d))
  else yp
termination_by c.size - d

/-- Julia `vandermondeinterp(x, y, N, grid)` (`composite.jl:877-885`, `Array` inputs):
the fit's coefficients, the grid `minimum(x):(maximum(x)-minimum(x))/grid:maximum(x)` and
the fitted polynomial on it (summed in Julia's order: `c₀ + c₁x + c₂x² + …`). -/
def vandermondeinterp (x y : FloatArray) (N grid : Nat) : FloatArray × FloatArray × FloatArray :=
  let coef := vandermondeFit x y N
  let minx := x.foldl F64.min (x.get! 0)
  let maxx := x.foldl F64.max (x.get! 0)
  let xp := (colon minx ((maxx - minx) / grid.toUInt64.toFloat) maxx).toFloatArray
  let yp := FloatArray.mk (Array.replicate xp.size (coef.get! 0))
  (coef, xp, interpLoop coef xp 1 yp)

end Grassmann.Forms
