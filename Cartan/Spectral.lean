import Cartan.Spectral.FFT
import Cartan.Solve.Dense
import Cartan.Algebra

/-!
# Spectral tools on grids (Cartan.jl `src/spectral.jl`, `ext/FFTWExt.jl`, `ext/ToeplitzMatricesExt.jl`)

Port notes: `docs/port-notes/cartan-element-spectral-plot.md` §2.2, §4.9. The transforms themselves
are `Cartan.Spectral.FFT` (FFTW's conventions); here are the frequency domains, the transforms of
fields, periodic spectral calculus, Chebyshev collocation, Clenshaw–Curtis weights, barycentric
Lagrange and sinc resampling, orthogonal series and the Laplace/Gabor transforms.

**Frequency domains.** Julia's `FourierSpace` remembers the physical domain so that `fft` and
`ifft` swap it back and forth (`fftspace(fftspace(x)) == x`). Here the base of a transformed
field is `fftBase a` (the grid of `fftAxis a`), a function of the physical axis `a`, so the
inverse transforms recover `a` from the *type* of their argument: `ifft (fft t)` is a field over
`t`'s own base with no runtime bookkeeping. The frequency values follow Julia bit for bit
(`fftspace(x) = (n/N)·rfftfreq(n, N·2π/(x[end]-x[1]))`, `n = 2(N−1) + iseven(N)`, B20: the step
is `2π/((N−1)h)`, not `2π/(Nh)`); frequency grids are clamped (`GridBundle(::FourierSpace)`).

**Julia defects fixed** (port notes §8.3):
* **B10** `fftwavenumber`, `spectral_diff_fft`, `spectral_sum_fft` of odd `N` list
  `[0 … (N−1)/2−1, −(N+1)/2 … −1]` (one frequency short, one too negative): here
  `[0 … (N−1)/2, −(N−1)/2 … −1]`, so odd-length periodic derivatives are exact;
* **B12** the axis of `fftshift` for even `N` is off by one bin from the data: here
  `ω·(−N/2 … N/2−1)`, matching the shifted data;
* **B13** `ChebyshevMatrix(::Chebyshev)` differentiates on the *descending* nodes, so
  `gradient_chebyshev` gives `−dv/dx`: `chebyshevMatrix` differentiates on the ascending points;
* **B14** `gradient2_chebyshevfft` uses `W₂/√(1−x²) − x W₁/(1−x²)^{3/4}` and zero endpoints: here the
  second derivative is the first-derivative transform applied twice (exact for polynomials of
  degree `< N`);
* **B9** `clenshawcurtis` has end weights `1/(N²+1)`/`0` (the sum is below 2): `clenshawcurtis`
  gives the standard weights, `clenshawcurtisJulia` Julia's;
* `iflt`: Julia multiplies by `exp(σ·ω)` on the frequency axis before `ifft` (not the inverse of
  `flt`); here `exp(σ t)·ifft(F)`;
* **B19** the default of `integral_fft` on curves is the *difference* vector, and a zero mean
  gives `NaN` (`0·∞`): `integralFFT` integrates with the sum vector and treats a zero mean;
* **B15** the Chebyshev series use no weight and map domains not starting at `0` outside
  `[−1, 1]`; the Fourier series (`FourierCosine`, `FourierSine`) are ported as Julia defines
  them (coefficients by the trapezoid rule, the constant term not halved on restore).
-/

namespace Cartan

open JuliaBase Cartan.Spectral Cartan.Solve

namespace Spectral

/-! ## Frequency axes (`spectral.jl:47-71`) -/

/-- Julia `fftspace(N, ω)` (`spectral.jl:52-56`): `k · ((n/N)·(Nω/n))`, `k < N`,
`n = 2(N−1) + iseven(N)` (AbstractFFTs `rfftfreq` scaled lazily). -/
def fftFreqs (N : Nat) (ω : Float) : FloatArray :=
  let n := 2 * (N - 1) + (if N % 2 == 0 then 1 else 0)
  let nf := n.toUInt64.toFloat
  let Nf := N.toUInt64.toFloat
  let mult := (nf / Nf) * ((Nf * ω) / nf)
  ⟨(Array.range N).map fun k => k.toUInt64.toFloat * mult⟩

/-- Julia `rfftspace(N, ω) = rfftfreq(N, N ω)`: `k · (Nω/N)`, `k ≤ N÷2`. -/
def rfftFreqs (N : Nat) (ω : Float) : FloatArray :=
  let Nf := N.toUInt64.toFloat
  let mult := (Nf * ω) / Nf
  ⟨(Array.range (N / 2 + 1)).map fun k => k.toUInt64.toFloat * mult⟩

/-- Julia `r2rspace(N, kind, fs)` (`spectral.jl:64-67`): `fftspace(N, 1/fs)`, shifted by one step
for the kinds whose frequencies start at `1` (`RODFT10`, `REDFT11`, `RODFT11`). -/
def r2rFreqs (N : Nat) (kind : R2RKind) (fs : Float) : FloatArray :=
  let out := fftFreqs N (1 / fs)
  if kind == .RODFT10 || kind == .REDFT11 || kind == .RODFT11 then
    let s := out.get! 1
    ⟨out.data.map (· + s)⟩
  else out

/-- The angular step `2π/(x[end]−x[1])` of the `fft`/`rfft` axis of a physical axis. -/
def fftOmega (a : Axis) : Float := twoPiF / (a.last - a.first)

/-- Julia `fftspace(x)` of a physical axis: its frequency axis. -/
def fftAxis (a : Axis) : Axis := .explicit (fftFreqs a.length (fftOmega a))

/-- Julia `rfftspace(x)`. -/
def rfftAxis (a : Axis) : Axis := .explicit (rfftFreqs a.length (fftOmega a))

/-- Julia `r2rspace(x, kind)`: `fs = (x[end]−x[1])/π`. -/
def r2rAxis (a : Axis) (kind : R2RKind) : Axis :=
  .explicit (r2rFreqs a.length kind ((a.last - a.first) / piF))

/-- Julia `r2rspace(x)` (no kind): `fftspace(N, π/(x[end]−x[1]))`. -/
def dctAxis (a : Axis) : Axis := .explicit (fftFreqs a.length (piF / (a.last - a.first)))

/-- The (clamped) frequency grid of `fft` fields over `a`. -/
def fftBase (a : Axis) : GridBundle 1 Float := (GridBundle.ofAxis (fftAxis a)).clamped

/-- The frequency grid of `rfft` fields over `a`. -/
def rfftBase (a : Axis) : GridBundle 1 Float := (GridBundle.ofAxis (rfftAxis a)).clamped

/-- The frequency grid of `r2r(·, kind)` fields over `a`. -/
def r2rBase (a : Axis) (kind : R2RKind) : GridBundle 1 Float := (GridBundle.ofAxis (r2rAxis a kind)).clamped

/-- The frequency grid of `dct`/`dst` fields over `a`. -/
def dctBase (a : Axis) : GridBundle 1 Float := (GridBundle.ofAxis (dctAxis a)).clamped

/-! ## Wavenumbers (`spectral.jl:767-784`) -/

/-- The FFT wavenumbers `[0, 1, …, ⌈N/2⌉−1, −⌊N/2⌋, …, −1]` (Julia `fftwavenumber(N)`, B10 fixed
for odd `N`). -/
def fftWavenumber (N : Nat) : Array Int :=
  (Array.range N).map fun k => if 2 * k < N then Int.ofNat k else Int.ofNat k - Int.ofNat N

/-- Julia's `fftwavenumber(N)` (for odd `N` one short and one too negative, B10). -/
def fftWavenumberJulia (N : Nat) : Array Int :=
  let a := (N - N % 2) / 2
  let b := (N + N % 2) / 2
  (Array.range a).map Int.ofNat ++ (Array.range b).map fun i => Int.ofNat i - Int.ofNat b

/-- Julia `rfftwavenumber(N) = 0:N÷2`. -/
def rfftWavenumber (N : Nat) : Array Int := (Array.range (N / 2 + 1)).map Int.ofNat

/-- Julia `r2rwavenumber(N, kind)`: `1:N` for the kinds starting at `1`, else `0:N−1`. -/
def r2rWavenumber (N : Nat) (kind : R2RKind) : Array Int :=
  let s : Int := if kind == .RODFT10 || kind == .REDFT11 || kind == .RODFT11 then 1 else 0
  (Array.range N).map fun k => Int.ofNat k + s

/-- An integer as a float. -/
@[inline] def intF (k : Int) : Float := Axis.intToFloat k

/-- Julia `spectral_diff_fft(N) = i·k` (B10 fixed). -/
def spectralDiffFFT (N : Nat) : CVec := CVec.ofReIm ⟨Array.replicate N 0⟩ ⟨(fftWavenumber N).map intF⟩

/-- Julia `spectral_diff_rfft(N) = i·(0:N÷2)`. -/
def spectralDiffRFFT (N : Nat) : CVec :=
  CVec.ofReIm ⟨Array.replicate (N / 2 + 1) 0⟩ ⟨(rfftWavenumber N).map intF⟩

/-- Julia `spectral_sum_fft(N) = −i·[0, 1/k…]` (B10 fixed). -/
def spectralSumFFT (N : Nat) : CVec :=
  CVec.ofReIm ⟨Array.replicate N 0⟩ ⟨(fftWavenumber N).map fun k => if k == 0 then 0 else -(1 / intF k)⟩

/-- Julia `spectral_sum_rfft(N) = −i·[0, 1/1, …, 1/(N÷2)]`. -/
def spectralSumRFFT (N : Nat) : CVec :=
  CVec.ofReIm ⟨Array.replicate (N / 2 + 1) 0⟩ ⟨(rfftWavenumber N).map fun k => if k == 0 then 0 else -(1 / intF k)⟩

/-- Julia `fftshift(x)` of data: `circshift(x, N÷2)` (bins `N−N÷2 …` first). -/
def fftshiftData (z : CVec) : CVec :=
  let N := z.len
  let s := N / 2
  ⟨(Array.range (2 * N)).map fun q => let k := q / 2; z.get! (2 * ((k + N - s) % N) + q % 2)⟩

/-- Julia `ifftshift(x) = circshift(x, −N÷2)`. -/
def ifftshiftData (z : CVec) : CVec :=
  let N := z.len
  let s := N / 2
  ⟨(Array.range (2 * N)).map fun q => let k := q / 2; z.get! (2 * ((k + s) % N) + q % 2)⟩

/-- The frequencies of the shifted data, `ω·(−N÷2 … ⌈N/2⌉−1)` (B12 fixed). -/
def fftshiftFreqs (N : Nat) (ω : Float) : FloatArray :=
  ⟨(Array.range N).map fun k => intF (Int.ofNat k - Int.ofNat (N / 2)) * ω⟩

/-! ## Periodic calculus on sample vectors (`spectral.jl:807-935`) -/

/-- `d ⊙ X` with Julia's promotion of `Complex{Int}` to `Complex{Float64}`. -/
def cmulInt (d X : CVec) : CVec := CVec.mul d X

/-- Julia `gradient_fft(t) = real(ifft(d .* fft(t)))`: the periodic derivative in the sample phase
`θ = 2πj/N` (B20: not rescaled to `x`). -/
def gradientFFT (x : FloatArray) : FloatArray :=
  CVec.realPart (ifft (cmulInt (spectralDiffFFT x.size) (fft (CVec.ofReal x))))

/-- Julia `gradient_rfft(t) = irfft(d .* rfft(t), N)`. -/
def gradientRFFT (x : FloatArray) : FloatArray :=
  irfft (cmulInt (spectralDiffRFFT x.size) (rfft x)) x.size

/-- The periodic antiderivative with Julia's mean correction (`spectral.jl:909-912`):
`out = real(ifft(d .* fft(t − m)))`, `out + m·(x − (x₀ + out[1]/m))` with `m = mean(t)`; for
`m = 0` the result is `out − out[1]` (Julia: `NaN`, B19). -/
def integralWith (inv : CVec → FloatArray) (fwd : FloatArray → CVec) (d : CVec) (xs x : FloatArray) :
    FloatArray :=
  let N := x.size
  let m := JuliaBase.F64.sum x / N.toUInt64.toFloat
  let out := inv (cmulInt d (fwd ⟨x.data.map (· - m)⟩))
  let o1 := out.get! 0
  let x0 := xs.get! 0
  if m == 0 then ⟨out.data.map (· - o1)⟩
  else ⟨(Array.range N).map fun i => out.get! i + m * (xs.get! i - (x0 + o1 / m))⟩

/-- Julia `integral_fft(t)` on the points `xs`. -/
def integralFFT (xs x : FloatArray) : FloatArray :=
  integralWith (fun X => CVec.realPart (ifft X)) (fun v => fft (CVec.ofReal v)) (spectralSumFFT x.size) xs x

/-- Julia `integral_rfft(t)` on the points `xs`. -/
def integralRFFT (xs x : FloatArray) : FloatArray :=
  integralWith (fun X => irfft X x.size) rfft (spectralSumRFFT x.size) xs x

/-- Julia `gradient_impulse(t) = real(irfft(i·(0:N÷2)))`: the circulant kernel of `d/dθ`. -/
def gradientImpulse (N : Nat) : FloatArray := irfft (spectralDiffRFFT N) N

/-- Julia `integral_impulse(t) = real(irfft(spectral_sum_rfft(N)))`. -/
def integralImpulse (N : Nat) : FloatArray := irfft (spectralSumRFFT N) N

/-- Julia `spectral_sum_impulse(N)` (`spectral.jl:930-934`): `(b/−x)·(0:N−1) + b`, `x = N/2`,
`b = (π/2)/x`. -/
def spectralSumImpulse (N : Nat) : FloatArray :=
  let x := N.toUInt64.toFloat / 2
  let b := (piF / 2) / x
  let s := b / -x
  ⟨(Array.range N).map fun k => s * k.toUInt64.toFloat + b⟩

/-- Julia `convolve(f, g) = irfft(rfft(f) .* rfft(g))`: circular convolution. -/
def convolve (f g : FloatArray) : FloatArray := irfft (CVec.mul (rfft f) (rfft g)) f.size

/-! ## Toeplitz differentiation matrices (`spectral.jl:1069-1072`, ToeplitzMatricesExt) -/

/-- `cot x`. -/
def cotF (x : Float) : Float := let (s, c) := JuliaBase.F64.sincos x; c / s

/-- Julia `toeplitz1(N, h = 2π/N) = [0; ½(−1)^k cot(kh/2)]`. -/
def toeplitz1 (N : Nat) (h : Float := twoPiF / N.toUInt64.toFloat) : FloatArray :=
  ⟨(Array.range N).map fun k => if k == 0 then 0 else
    (if k % 2 == 1 then -0.5 else 0.5) * cotF (k.toUInt64.toFloat * h / 2)⟩

/-- Julia `toeplitz2(N, h) = [−π²/(3h²) − 1/6; ½(−1)^{k+1}/sin²(kh/2)]`. -/
def toeplitz2 (N : Nat) (h : Float := twoPiF / N.toUInt64.toFloat) : FloatArray :=
  ⟨(Array.range N).map fun k => if k == 0 then -(piF * piF) / (3 * (h * h)) - 1 / 6 else
    let s := JuliaBase.F64.sin (k.toUInt64.toFloat * h / 2)
    (if k % 2 == 1 then 0.5 else -0.5) / (s * s)⟩

/-- Julia `derivetoeplitz(N) = Toeplitz(c, −c)`: `D[i,j] = c[i−j]` below, `−c[j−i]` above. -/
def derivetoeplitz (N : Nat) : Dense :=
  let c := toeplitz1 N
  Dense.ofFn N N fun i j => if i ≥ j then c.get! (i - j) else -(c.get! (j - i))

/-- Julia `derivetoeplitz2(N) = Toeplitz(c, c)` (symmetric). -/
def derivetoeplitz2 (N : Nat) : Dense :=
  let c := toeplitz2 N
  Dense.ofFn N N fun i j => c.get! (if i ≥ j then i - j else j - i)

/-! ## Chebyshev collocation (`spectral.jl:319-393, 937-1064`) -/

/-- Julia `Chebyshev(N)`: the angles `θ = (π/(N−1))·(0:N−1)` (a `StepRangeLen`) and the ascending
Chebyshev–Lobatto points `x = −cos θ`. -/
def chebyshevAngles (N : Nat) : Axis :=
  .stepLen (JuliaBase.rangeStep 0 (piF / (N - 1).toUInt64.toFloat) N)

/-- Julia `points(Chebyshev(N))`. -/
def chebyshevPoints (N : Nat) : FloatArray :=
  let θ := chebyshevAngles N
  ⟨(Array.range N).map fun k => -(JuliaBase.F64.cos (θ.get k))⟩

/-- Julia `Chebyshev(x)`: the points mapped affinely onto `[x₀, x_end]`,
`(c + 1)·((x_end − x₀)/2) + x₀`. -/
def chebyshevOn (N : Nat) (x0 x1 : Float) : FloatArray :=
  let s := (x1 - x0) / 2
  ⟨(chebyshevPoints N).data.map fun c => (c + 1) * s + x0⟩

/-- Julia `unitpoints(t)`: back to `[−1, 1]`, `(x − x₀)·(2/(x_end − x₀)) − 1`. -/
def unitpoints (x : FloatArray) : FloatArray :=
  let x0 := x.get! 0
  let s := 2 / (x.get! (x.size - 1) - x0)
  ⟨x.data.map fun v => (v - x0) * s - 1⟩

/-- Julia `ChebyshevMatrix(x)` (`spectral.jl:355-361`): the barycentric differentiation matrix on the
nodes `x`, `D_ij = (c_i/c_j)/(x_i − x_j)` (`c = [2, 1, …, 1, 2]·(−1)^j`), diagonal `1 − Σ_j D_ij`
(Julia adds `I` before dividing, so the pre-correction diagonal is `1`, and subtracts the row sums
including it). -/
def chebyshevMatrixOn (x : FloatArray) : Dense := Id.run do
  let n := x.size
  let N := n - 1
  let c : FloatArray := ⟨(Array.range n).map fun j =>
    let a : Float := if j == 0 || j == N then 2 else 1
    if j % 2 == 1 then -a else a⟩
  let D0 := Dense.ofFn n n fun i j =>
    let num := c.get! i * (1 / c.get! j)
    num / ((x.get! i - x.get! j) + (if i == j then 1 else 0))
  let mut D := D0
  for i in [0:n] do
    let s := (List.range n).foldl (fun acc j => if j == 0 then D0.get i 0 else acc + D0.get i j) 0
    D := D.set i i (D0.get i i - s)
  return D

/-- Julia `ChebyshevMatrix(N::Int)` (`spectral.jl:354`): the matrix on the *descending* nodes
`−points(Chebyshev(N))` (Trefethen's `cheb(N−1)`; applied to data on the ascending points it gives
`−d/dx`, B13); `[0;;]` for `N = 0`. -/
def chebyshevMatrixJulia (N : Nat) : Dense :=
  if N == 0 then Dense.zeros 1 1 else chebyshevMatrixOn ⟨(chebyshevPoints N).data.map (- ·)⟩

/-- The differentiation matrix on the ascending Chebyshev points (B13 fixed): `D v ≈ dv/dx`. -/
def chebyshevMatrix (N : Nat) : Dense :=
  if N == 0 then Dense.zeros 1 1 else chebyshevMatrixOn (chebyshevPoints N)

/-- Julia `ChebyshevVector(x, N)` (`spectral.jl:350`): `[0; reverse(inv(D[1:N−1, 1:N−1])[1, :])]`
(integration weights `w·v ≈ ∫_{−1}^{1} v` for Julia's descending-node matrix). -/
def chebyshevVectorOf (D : Dense) : FloatArray :=
  let N := D.rows
  let sub := Dense.ofFn (N - 1) (N - 1) fun i j => D.get i j
  let Iv := sub.inv
  ⟨#[0] ++ ((Array.range (N - 1)).map fun j => Iv.get 0 j).reverse⟩

/-- Julia `ChebyshevVector(N)`. -/
def chebyshevVector (N : Nat) : FloatArray := chebyshevVectorOf (chebyshevMatrixJulia N)

/-- Julia `chebyshevfft(v) = fft([v; reverse(v[2:N−1])])`: the FFT of the even extension. -/
def chebyshevfft (v : FloatArray) : CVec :=
  let N := v.size
  let ext : FloatArray := ⟨v.data ++ ((Array.range (N - 2)).map fun k => v.get! (N - 2 - k))⟩
  fft (CVec.ofReal ext)

/-- Julia `spectral_diff_chebfft(N) = i·[0:N−2, 0, 2−N:−1]` (length `2N−2`). -/
def spectralDiffChebFFT (N : Nat) : CVec :=
  let ks : Array Int := (Array.range (N - 1)).map Int.ofNat ++ #[0] ++
    (Array.range (N - 2)).map fun i => Int.ofNat i + 2 - Int.ofNat N
  CVec.ofReIm ⟨Array.replicate ks.size 0⟩ ⟨ks.map intF⟩

/-- Julia `chebyshevifft(V, U, N)` (`spectral.jl:385-394`): the back half of Trefethen's `chebfft`. -/
def chebyshevifft (V : CVec) (U : FloatArray) (N : Nat) : FloatArray := Id.run do
  let W := CVec.realPart (ifft V)
  let Nm := (N - 1).toUInt64.toFloat
  let mut w : FloatArray := ⟨Array.replicate N 0⟩
  for k in [1:N - 1] do
    let (c, _) := cossinpiRat k (N - 1)
    w := w.set! k (-(W.get! k) / Float.sqrt (1.0 - c * c))
  -- w[1] = sum(ii.^2 .* U[ii+1])/(N−1) + (0.5(N−1))·U[N]
  let terms : FloatArray := ⟨(Array.range (N - 1)).map fun i => (i * i).toUInt64.toFloat * U.get! i⟩
  let s1 := JuliaBase.F64.sum terms
  w := w.set! 0 (s1 / Nm + (0.5 * Nm) * U.get! (N - 1))
  let terms2 : FloatArray := ⟨(Array.range (N - 1)).map fun i =>
    (if (i + 1) % 2 == 1 then -1.0 else 1.0) * (i * i).toUInt64.toFloat * U.get! i⟩
  let s2 := JuliaBase.F64.sum terms2
  let sgn : Float := if N % 2 == 1 then -1 else 1
  w := w.set! (N - 1) (s2 / Nm + 0.5 * Nm * sgn * U.get! (N - 1))
  return w

/-- Julia `gradient_chebyshevfft(v)` (`spectral.jl:939-942`): `dv/du` on the ascending
Chebyshev–Lobatto points `u ∈ [−1, 1]` (exact for polynomials of degree `< N`). -/
def gradientChebyshevFFT (v : FloatArray) : FloatArray :=
  let N := v.size
  let U : FloatArray := ⟨(CVec.realPart (chebyshevfft v)).data.map (- ·)⟩
  chebyshevifft (cmulInt (spectralDiffChebFFT N) (CVec.ofReal U)) U N

/-- The second derivative on the Chebyshev points: `gradientChebyshevFFT` applied twice (B14 fixed:
Julia's `gradient2_chebyshevfft` has wrong powers and zero endpoints). -/
def gradient2ChebyshevFFT (v : FloatArray) : FloatArray := gradientChebyshevFFT (gradientChebyshevFFT v)

/-- Julia `gradient_chebyshev(v, D) = D * v` with the ascending-node matrix (B13 fixed). -/
def gradientChebyshev (v : FloatArray) : FloatArray := (chebyshevMatrix v.size).mulVec v

/-- Julia `clenshawcurtis(n)` (`spectral.jl:1081-1104`, faithful: end weights `1/(N²+1)` or `1/N²`
and `0`, B9), reversed. -/
def clenshawcurtisJulia (n : Nat) : FloatArray := Id.run do
  let N := n - 1
  let Nf := N.toUInt64.toFloat
  let θ := fun (k : Nat) => piF * k.toUInt64.toFloat / Nf
  let mut w : FloatArray := ⟨Array.replicate (N + 1) 0⟩
  let mut v : FloatArray := ⟨Array.replicate (N - 1) 1⟩
  if N % 2 == 0 then
    w := w.set! 0 (1 / (Nf * Nf + 1))
    for k in [1:N / 2] do
      let kf := k.toUInt64.toFloat
      for i in [0:N - 1] do
        v := v.set! i (v.get! i - 2 * JuliaBase.F64.cos (2 * kf * θ (i + 1)) / (4 * kf * kf - 1))
    for i in [0:N - 1] do
      v := v.set! i (v.get! i - JuliaBase.F64.cos (Nf * θ (i + 1)) / (Nf * Nf - 1))
  else
    w := w.set! 0 (1 / (Nf * Nf))
    for k in [1:(N - 1) / 2 + 1] do
      let kf := k.toUInt64.toFloat
      for i in [0:N - 1] do
        v := v.set! i (v.get! i - 2 * JuliaBase.F64.cos (2 * kf * θ (i + 1)) / (4 * kf * kf - 1))
  for i in [0:N - 1] do
    w := w.set! (i + 1) ((2 / Nf) * v.get! i)
  return ⟨w.data.reverse⟩

/-- The standard Clenshaw–Curtis weights on `n` Chebyshev points (B9 fixed: both end weights
`1/(N²−1)` for even `N`, `1/N²` for odd), in ascending point order; `Σ w = 2`. -/
def clenshawcurtis (n : Nat) : FloatArray := Id.run do
  let N := n - 1
  let Nf := N.toUInt64.toFloat
  let θ := fun (k : Nat) => piF * k.toUInt64.toFloat / Nf
  let mut v : FloatArray := ⟨Array.replicate (N - 1) 1⟩
  let e := if N % 2 == 0 then 1 / (Nf * Nf - 1) else 1 / (Nf * Nf)
  if N % 2 == 0 then
    for k in [1:N / 2] do
      let kf := k.toUInt64.toFloat
      for i in [0:N - 1] do
        v := v.set! i (v.get! i - 2 * JuliaBase.F64.cos (2 * kf * θ (i + 1)) / (4 * kf * kf - 1))
    for i in [0:N - 1] do
      v := v.set! i (v.get! i - JuliaBase.F64.cos (Nf * θ (i + 1)) / (Nf * Nf - 1))
  else
    for k in [1:(N - 1) / 2 + 1] do
      let kf := k.toUInt64.toFloat
      for i in [0:N - 1] do
        v := v.set! i (v.get! i - 2 * JuliaBase.F64.cos (2 * kf * θ (i + 1)) / (4 * kf * kf - 1))
  let inner := (Array.range (N - 1)).map fun i => (2 / Nf) * v.get! i
  return ⟨#[e] ++ inner.reverse ++ #[e]⟩

/-! ## Barycentric Lagrange and sinc resampling (`spectral.jl:523-760`) -/

/-- Julia `prod(v)` of a short vector, left to right (`1.0` when empty). -/
def prodL (v : List Float) : Float := match v with | [] => 1 | x :: xs => xs.foldl (· * ·) x

/-- Julia `lagrangeweights(v, j) = inv(prod(out[1:j−1])·prod(out[j+1:end]))`, `out = v_j .− v`. -/
def lagrangeweight (v : FloatArray) (j : Nat) : Float :=
  let vj := v.get! j
  let out := (List.range v.size).map fun i => vj - v.get! i
  1 / (prodL (out.take j) * prodL (out.drop (j + 1)))

/-- Julia `lagrangeweights(v)`. -/
def lagrangeweights (v : FloatArray) : FloatArray := ⟨(Array.range v.size).map (lagrangeweight v)⟩

/-- Julia `lagrangepolynomial(v, wy, x) = prod(x .− v)·sum(wy ./ (x .− v))` (the first barycentric
form; `NaN` at a node). `prod`/`sum` are Julia's (pairwise beyond 16 terms). -/
def lagrangeAt (v wy : FloatArray) (x : Float) : Float :=
  let xv : FloatArray := ⟨v.data.map (x - ·)⟩
  TensorField.prodFloats xv * JuliaBase.F64.sum ⟨(Array.range v.size).map fun i => wy.get! i / xv.get! i⟩

/-- Julia `lagrangepolynomial(t, x)` for node values `y` on nodes `v`: the interpolant at every `x`,
the node value where the formula gives `NaN` (Julia falls back to `t(x)`). -/
def lagrangepolynomial (v y xs : FloatArray) : FloatArray :=
  let w := lagrangeweights v
  let wy : FloatArray := ⟨(Array.range v.size).map fun i => w.get! i * y.get! i⟩
  ⟨xs.data.map fun x =>
    let p := lagrangeAt v wy x
    if p != p then
      match (List.range v.size).find? (fun i => v.get! i == x) with
      | some i => y.get! i
      | none => p
    else p⟩

/-- Julia `rootspolynomial(v, x) = prod(x .− v)` (the nodal polynomial). -/
def rootspolynomial (v : FloatArray) (x : Float) : Float := TensorField.prodFloats ⟨v.data.map (x - ·)⟩

/-- Julia `sinc(x) = sin(πx)/(πx)` (`1` at `0`, Julia's `sinpi`). -/
def sincF (x : Float) : Float :=
  if x == 0 then 1 else if x.isInf then 0 else JuliaBase.F64.sinpi x / (piF * x)

/-- Julia `resample_sinc(v, n)` on a range axis `a` (`spectral.jl:523-533`): the Whittaker–Shannon
interpolant `Σᵢ yᵢ sinc((x − xᵢ)/h)` at the `n` points of `resample(a, n)`, accumulated per node
(`p += yᵢ sinc.(…)`); the axes are divided by `h` first, as Julia does. -/
def resampleSinc (a : Axis) (y : FloatArray) (n : Nat) : Axis × FloatArray :=
  let h := (a.step?).getD 1
  let xx := a.resample n
  let xh := ((a.div h).getD (.explicit ⟨a.toFloatArray.data.map (· / h)⟩))
  let xxh := ((xx.div h).getD (.explicit ⟨xx.toFloatArray.data.map (· / h)⟩))
  let p := (List.range a.length).foldl (fun (p : FloatArray) i =>
    let yi := y.get! i
    let xi := xh.get i
    ⟨(Array.range n).map fun k => p.get! k + yi * sincF (xxh.get k - xi)⟩) ⟨Array.replicate n 0⟩
  (xx, p)

/-! ## Orthogonal series (`spectral.jl:202-315`) -/

/-- Julia `OrthogonalTransform{F,T}`: a basis `f(n, x)` on the canonical interval `[a, b]`. -/
structure OrthogonalTransform where
  /-- The basis function. -/
  f : Nat → Float → Float
  /-- Left end. -/
  a : Float
  /-- Right end. -/
  b : Float

/-- Julia `FourierCosine = OT((n,x) -> cos(n x), 0, π)`. -/
def FourierCosine : OrthogonalTransform := ⟨fun n x => JuliaBase.F64.cos (n.toUInt64.toFloat * x), 0, piF⟩

/-- Julia `FourierSine = OT((n,x) -> sin((n+1) x), 0, π)`. -/
def FourierSine : OrthogonalTransform := ⟨fun n x => JuliaBase.F64.sin ((n + 1).toUInt64.toFloat * x), 0, piF⟩

/-- Julia `ChebyshevFirst = OT((n,x) -> cos(n acos x), −1, 1)`. -/
def ChebyshevFirst : OrthogonalTransform :=
  ⟨fun n x => JuliaBase.F64.cos (n.toUInt64.toFloat * JuliaBase.F64.acos x), -1, 1⟩

/-- Julia `ChebyshevSecond` with the removable singularity at `x = 1` evaluated correctly
(`Uₙ(1) = n + 1`; Julia returns `1`, B15). -/
def ChebyshevSecond : OrthogonalTransform :=
  ⟨fun n x =>
    let θ := JuliaBase.F64.acos x
    if θ == 0 then (n + 1).toUInt64.toFloat
    else JuliaBase.F64.sin ((n + 1).toUInt64.toFloat * θ) / JuliaBase.F64.sin θ, -1, 1⟩

/-- The trapezoid rule on explicit points (Julia `trapz(f) = sum((diff(x)/2) .* (g[2:end] + g[1:end-1]))`). -/
def trapz (xs g : FloatArray) : Float :=
  JuliaBase.F64.sum ⟨(Array.range (xs.size - 1)).map fun i =>
    ((xs.get! (i + 1) - xs.get! i) / 2) * (g.get! (i + 1) + g.get! i)⟩

/-- Julia `(f::OrthogonalTransform)(g, N)` forward (`spectral.jl:229-234`): the first `N` series
coefficients `cₙ = (2/L) ∫ g f(n, ωx)`, `ωx = ((b−a)/L) x + a`, `L = x_end − x₀`. -/
def seriesCoefficients (T : OrthogonalTransform) (xs g : FloatArray) (N : Nat) : FloatArray :=
  let L := xs.get! (xs.size - 1) - xs.get! 0
  let s := (T.b - T.a) / L
  let ωx : FloatArray := ⟨xs.data.map fun x => s * x + T.a⟩
  ⟨(Array.range N).map fun n =>
    (2 / L) * trapz xs ⟨(Array.range xs.size).map fun i => g.get! i * T.f n (ωx.get! i)⟩⟩

/-- Julia `(f::OrthogonalTransform)(g)` restore (`spectral.jl:221-228`): `Σₙ cₙ f(n−1, ωx)` on the
physical points (the constant term not halved, as Julia). -/
def seriesRestore (T : OrthogonalTransform) (xs c : FloatArray) : FloatArray :=
  let L := xs.get! (xs.size - 1) - xs.get! 0
  let s := (T.b - T.a) / L
  ⟨xs.data.map fun x =>
    let ωx := s * x + T.a
    (List.range c.size).foldl (fun acc n =>
      let t := c.get! n * T.f n ωx
      if n == 0 then t else acc + t) 0⟩

end Spectral

/-! ## Transforms of fields (`spectral.jl:83-94`, FFTWExt) -/

namespace TensorField

open Spectral

variable {a : Axis}

/-- The complex values of a field as interleaved `(re, im)` data (the `Complex` flat layout). -/
@[inline] def cdata {M : Type} [FrameBundle M] {m : M} (t : TensorField m (Complex Float)) : CVec := t.data

/-- A complex field from interleaved data (the zero field if the length disagrees). -/
def ofCVec {M : Type} [FrameBundle M] (m : M) (z : CVec) : TensorField m (Complex Float) :=
  (TensorField.ofFlat? m z).getD default

/-- A real field from its values (the zero field if the length disagrees). -/
def ofReals {M : Type} [FrameBundle M] (m : M) (x : FloatArray) : TensorField m Float :=
  (TensorField.ofFlat? m x).getD default

/-- Julia `fft(t)` of a real field over the axis `a`: a complex field over `fftspace(a)`. -/
def fft (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (fftBase a) (Complex Float) :=
  ofCVec _ (Spectral.fft (CVec.ofReal t.data))

/-- Julia `fft(t)` of a complex field. -/
def fftC (t : TensorField (GridBundle.ofAxis a) (Complex Float)) : TensorField (fftBase a) (Complex Float) :=
  ofCVec _ (Spectral.fft t.cdata)

/-- Julia `ifft(t)`: back to the physical axis (read off the type). -/
def ifft (t : TensorField (fftBase a) (Complex Float)) : TensorField (GridBundle.ofAxis a) (Complex Float) :=
  ofCVec _ (Spectral.ifft t.cdata)

/-- Julia `bfft(t)`. -/
def bfft (t : TensorField (fftBase a) (Complex Float)) : TensorField (GridBundle.ofAxis a) (Complex Float) :=
  ofCVec _ (Spectral.bfft t.cdata)

/-- Julia `rfft(t)`. -/
def rfft (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (rfftBase a) (Complex Float) :=
  ofCVec _ (Spectral.rfft t.data)

/-- Julia `irfft(t)` (the length from the physical axis, Julia `invdim`). -/
def irfft (t : TensorField (rfftBase a) (Complex Float)) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.irfft t.cdata a.length)

/-- Julia `brfft(t)`. -/
def brfft (t : TensorField (rfftBase a) (Complex Float)) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.brfft t.cdata a.length)

/-- FFTWExt `r2r(t, kind)`: over `r2rspace(a, kind)`. -/
def r2r (t : TensorField (GridBundle.ofAxis a) Float) (kind : R2RKind) :
    TensorField (r2rBase a kind) Float := ofReals _ (Spectral.r2r t.data kind)

/-- FFTWExt `dct(t)` (orthonormal DCT-II) over `r2rspace(a)`. -/
def dct (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (dctBase a) Float :=
  ofReals _ (Spectral.dct t.data)

/-- FFTWExt `idct(t)`. -/
def idct (t : TensorField (dctBase a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.idct t.data)

/-- FFTWExt `dst(t) = r2r(t, RODFT10)/(2N)`. -/
def dst (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (r2rBase a .RODFT10) Float :=
  let s := 1 / (2 * a.length.toUInt64.toFloat)
  ofReals _ ⟨(Spectral.r2r t.data .RODFT10).data.map (· * s)⟩

/-- FFTWExt `idst(t) = r2r(t, RODFT01)` (the inverse of `dst`). -/
def idst (t : TensorField (r2rBase a .RODFT10) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.r2r t.data .RODFT01)

/-- Julia `gradient_fft(t)` of a real periodic field (derivative in the sample phase, B10/B20). -/
def gradientFFT (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.gradientFFT t.data)

/-- Julia `gradient_rfft(t)`. -/
def gradientRFFT (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.gradientRFFT t.data)

/-- Julia `integral_fft(t)`. -/
def integralFFT (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.integralFFT a.toFloatArray t.data)

/-- Julia `integral_rfft(t)`. -/
def integralRFFT (t : TensorField (GridBundle.ofAxis a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.integralRFFT a.toFloatArray t.data)

/-- Julia `integrate_fft(t)`: the last value of `integral_fft`. -/
def integrateFFT (t : TensorField (GridBundle.ofAxis a) Float) : Float :=
  let v := Spectral.integralFFT a.toFloatArray t.data
  v.get! (v.size - 1)

/-- Julia `convolve(f, g)`: circular convolution of two fields on the same axis. -/
def convolve (f g : TensorField (GridBundle.ofAxis a) Float) : TensorField (GridBundle.ofAxis a) Float :=
  ofReals _ (Spectral.convolve f.data g.data)

/-- Julia `flt(f, σ) = fft(exp(−σ t) f)`: the discrete Laplace transform at the damping `σ`. -/
def flt (f : TensorField (GridBundle.ofAxis a) Float) (σ : Float) : TensorField (fftBase a) (Complex Float) :=
  ofCVec _ (Spectral.fft (CVec.ofReal ⟨(Array.range a.length).map fun i =>
    JuliaBase.F64.exp ((-σ) * a.get i) * f.data.get! i⟩))

/-- The inverse of `flt`: `exp(σ t) · ifft(F)`. Julia's `iflt(F, σ) = ifft(exp(σ·t)·F)` (`spectral.jl:106`)
multiplies by `exp(σ·ω)` over the *frequency* axis before inverting, so `iflt(flt(s, σ), σ) ≠ s`;
fixed. -/
def iflt (F : TensorField (fftBase a) (Complex Float)) (σ : Float) : TensorField (GridBundle.ofAxis a) (Complex Float) :=
  let z := Spectral.ifft F.cdata
  ofCVec _ ⟨(Array.range (2 * a.length)).map fun q =>
    JuliaBase.F64.exp (σ * a.get (q / 2)) * z.get! q⟩

/-- Julia `fgt(f, σ, g)`: the windowed (Gabor) transform, one FFT row per window center `σᵢ`, row
`i` = `fft(g(t − σᵢ) f)`, as an array of complex rows. -/
def fgt (f : TensorField (GridBundle.ofAxis a) Float) (σs : FloatArray) (g : Float → Float) : Array CVec :=
  σs.data.map fun s => Spectral.fft (CVec.ofReal ⟨(Array.range a.length).map fun i =>
    g (a.get i - s) * f.data.get! i⟩)

end TensorField

end Cartan
