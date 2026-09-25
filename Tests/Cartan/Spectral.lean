import Tests.Cartan.Solve
import Cartan.Spectral

/-!
# Spectral tools (`oracle/golden/cartan/element/spectral.json`)

Generator `oracle/cartan/element/spectral.jl` (Cartan.jl `src/spectral.jl` with FFTW and
ToeplitzMatrices). Frequency axes, wavenumbers, Toeplitz matrices, Chebyshev points, matrices
and weights, Clenshaw–Curtis (Julia's variant), Lagrange weights and interpolation are compared
bit for bit or to a few ulps; everything that goes through an FFT to `1e-13` of the largest
value. Fixed Julia defects are checked against the correct values instead: odd-`N` wavenumbers
(B10: `gradient_fft(sin 3θ)` on 7 points is `3 cos 3θ`), the ascending-node Chebyshev derivative
(B13) and the second derivative (B14).
-/

open Lean Tests.Small Cartan JuliaBase Cartan.Spectral
open Tests.CartanTests.SolveTests (checkRel)

namespace Tests.CartanTests.SpectralTests

/-- Integers from a golden array. -/
def jInts (j : Json) : TestM (Array Int) := do (← jArr j).mapM jInt

/-- Run the spectral checks. -/
def run : TestM Unit := do
  let g ← load "element/spectral"
  let fl (j : Json) (k : String) : TestM FloatArray := do gFloats (← jField j k)
  -- 1. frequency axes
  for N in [1:13] do
    let Nf := N.toUInt64.toFloat
    checkFloats s!"spectral fftspace({N})" (fftFreqs N (1 / Nf)) (← fl (← jField g "fftspaceN") (toString N))
    checkFloats s!"spectral rfftspace({N})" (rfftFreqs N (1 / Nf)) (← fl (← jField g "rfftspaceN") (toString N))
  for N in [2:10] do
    for (k, kind) in [(5, R2RKind.REDFT10), (6, .REDFT11), (9, .RODFT10), (10, .RODFT11)] do
      checkFloats s!"spectral r2rspace({N},{k})" (r2rFreqs N kind 1)
        (← fl (← jField g "r2rspaceNk") s!"{N},{k}")
  let axes ← jField g "axes"
  for (key, a) in [("0:0.5:3.5", Axis.colon 0 0.5 3.5), ("range(-pi,pi,9)", Axis.range (-piF) piF 9),
      ("0.3:0.2:7.1", Axis.colon 0.3 0.2 7.1)] do
    let j ← jField axes key
    checkFloats s!"spectral fftspace {key}" (fftAxis a).toFloatArray (← fl j "fft")
    checkFloats s!"spectral rfftspace {key}" (rfftAxis a).toFloatArray (← fl j "rfft")
    checkFloats s!"spectral r2rspace {key}" (dctAxis a).toFloatArray (← fl j "r2r")
    checkFloats s!"spectral r2rspace9 {key}" (r2rAxis a .RODFT10).toFloatArray (← fl j "r2r9")
    checkFloats s!"spectral r2rspace5 {key}" (r2rAxis a .REDFT10).toFloatArray (← fl j "r2r5")
  -- wavenumbers: Julia's odd-N list is B10; ours is the correct one
  for N in [1:11] do
    let w ← jInts (← jField (← jField g "fftwavenumber") (toString N))
    check s!"spectral fftwavenumber({N}) (Julia's list)" (fftWavenumberJulia N == w)
    if N % 2 == 0 then check s!"spectral fftwavenumber({N})" (fftWavenumber N == w)
    let r ← jInts (← jField (← jField g "rfftwavenumber") (toString N))
    check s!"spectral rfftwavenumber({N})" (rfftWavenumber N == r)
  -- 2. Toeplitz, impulses
  checkFloats "spectral toeplitz1(8)" (toeplitz1 8) (← fl g "toeplitz1") libm
  checkFloats "spectral toeplitz2(8)" (toeplitz2 8) (← fl g "toeplitz2") libm
  checkFloats "spectral toeplitz1(7)" (toeplitz1 7) (← fl g "toeplitz1_7") libm
  checkFloats "spectral derivetoeplitz(4)" (derivetoeplitz 4).data (← fl g "derivetoeplitz4") libm
  checkFloats "spectral spectral_sum_impulse(8)" (spectralSumImpulse 8) (← fl g "spectral_sum_impulse")
  -- 3. periodic calculus on N = 8
  let g8 ← jField g "grid8"
  let a := Axis.colon 0 (twoPiF / 8) (7 * twoPiF / 8)
  checkFloats "spectral grid8 x" a.toFloatArray (← fl g8 "x")
  let t := TensorField.ofAxis a
  let s := TensorField.ofAxisFn a F64.sin
  checkFloats "spectral grid8 sin" s.data (← fl g8 "sin")
  let tol := 1e-13
  checkRel "spectral fft(sin)" s.fft.data (← fl g8 "fft") tol
  checkFloats "spectral fft axis" (fftAxis a).toFloatArray (← fl g8 "fftaxis")
  checkRel "spectral dct(sin)" s.dct.data (← fl g8 "dct") tol
  checkFloats "spectral dct axis" (dctAxis a).toFloatArray (← fl g8 "dctaxis")
  checkRel "spectral dst(sin)" s.dst.data (← fl g8 "dst") tol
  checkFloats "spectral dst axis" (r2rAxis a .RODFT10).toFloatArray (← fl g8 "dstaxis")
  checkRel "spectral idst(dst(sin))" s.dst.idst.data (← fl g8 "idst") tol
  checkRel "spectral rfft(sin)" s.rfft.data (← fl g8 "rfft") tol
  checkRel "spectral irfft(rfft(sin))" s.rfft.irfft.data (← fl g8 "irfft") tol
  checkRel "spectral gradient_impulse" (gradientImpulse 8) (← fl g8 "gradient_impulse") tol
  checkRel "spectral convolve(sin,sin)" (s.convolve s).data (← fl g8 "convolve") tol
  let c1 := TensorField.ofAxisFn a fun x => F64.cos x + 1
  checkRel "spectral integral_fft(cos+1)" c1.integralFFT.data (← fl g8 "integral_fft") tol
  checkRel "spectral integral_rfft(cos+1)" c1.integralRFFT.data (← fl g8 "integral_rfft") tol
  let intF ← gFloat (← jField g8 "integrate_fft")
  check "spectral integrate_fft" ((c1.integrateFFT - intF).abs ≤ 1e-13 * intF.abs)
  let a3 := (a.scale 3).getD a
  let s3 : TensorField (GridBundle.ofAxis a) Float :=
    TensorField.ofReals _ ⟨(Array.range a.length).map fun i => F64.sin (a3.get i)⟩
  checkRel "spectral gradient_fft(sin 3t)" s3.gradientFFT.data (← fl g8 "gradient_fft") tol
  checkRel "spectral gradient_rfft(sin 3t)" s3.gradientRFFT.data (← fl g8 "gradient_rfft") tol
  checkRel "spectral flt(sin, 0.5)" (s.flt 0.5).data (← fl g8 "flt") tol
  -- Julia's `iflt(F, σ) = ifft(exp(σ·t)·F)` multiplies by `exp(σ·ω)` on the *frequency* axis before
  -- inverting (so `iflt(flt(s)) ≠ s`); the port inverts `flt`: `exp(σ t)·ifft(F)`
  checkRel "spectral iflt(flt(sin)) = sin (Julia's iflt fixed)" ((s.flt 0.5).iflt 0.5).data
    (CVec.ofReal s.data) tol
  let _ ← fl g8 "iflt"
  let _ := t
  -- odd N: B10 fixed
  let g7 ← jField g "grid7"
  let a7 := Axis.colon 0 (twoPiF / 7) (6 * twoPiF / 7)
  let sin1 := TensorField.ofAxisFn a7 F64.sin
  checkRel "spectral grid7 gradient_fft(sin t)" sin1.gradientFFT.data (← fl g7 "gradient_fft_sin1") tol
  let sin3 : FloatArray := ⟨(Array.range 7).map fun i => F64.sin (3 * a7.get i)⟩
  let want3 : FloatArray := ⟨(Array.range 7).map fun i => 3 * F64.cos (3 * a7.get i)⟩
  checkRel "spectral grid7 gradient_fft(sin 3t) = 3cos 3t (B10 fixed)" (gradientFFT sin3) want3 1e-12
  -- 4. Chebyshev
  checkFloats "spectral Chebyshev(5)" (chebyshevPoints 5) (← fl g "chebyshev5") libm
  checkFloats "spectral Chebyshev(0:0.5:2)" (chebyshevOn 5 0 2) (← fl g "chebyshev_range") libm
  checkFloats "spectral unitpoints" (unitpoints (chebyshevOn 5 0 2)) (← fl g "unitpoints") libm
  for N in [2:10] do
    checkRel s!"spectral ChebyshevMatrix({N})" (chebyshevMatrixJulia N).data
      (← fl (← jField g "chebmatrix") (toString N)) 1e-14
  for N in [3:10] do
    checkRel s!"spectral ChebyshevVector({N})" (chebyshevVector N) (← fl (← jField g "chebvector") (toString N)) 1e-12
  let x9 := chebyshevPoints 9
  checkRel "spectral chebyshevfft(x³)" (chebyshevfft ⟨x9.data.map fun x => x * x * x⟩) (← fl g "chebfft9") tol
  let gc ← jField g "gradcheb9"
  checkRel "spectral gradient_chebyshevfft(x³)" (gradientChebyshevFFT ⟨x9.data.map fun x => x * x * x⟩)
    (← fl gc "x3") 1e-12
  checkRel "spectral gradient_chebyshevfft(x⁵-2x)"
    (gradientChebyshevFFT ⟨x9.data.map fun x => x * x * x * x * x - 2 * x⟩) (← fl gc "x5") 1e-12
  -- B13/B14 fixed: derivatives on the ascending points
  checkRel "spectral gradient_chebyshev(x³) = 3x² (B13 fixed)"
    (gradientChebyshev ⟨x9.data.map fun x => x * x * x⟩) ⟨x9.data.map fun x => 3 * x * x⟩ 1e-12
  checkRel "spectral gradient2_chebyshevfft(x⁴) = 12x² (B14 fixed)"
    (gradient2ChebyshevFFT ⟨x9.data.map fun x => x * x * x * x⟩) ⟨x9.data.map fun x => 12 * x * x⟩ 1e-11
  for n in [3:13] do
    checkRel s!"spectral clenshawcurtis({n}) (Julia)" (clenshawcurtisJulia n)
      (← fl (← jField g "clenshawcurtis") (toString n)) 1e-14
    let w := clenshawcurtis n
    check s!"spectral clenshawcurtis({n}) sums to 2 (B9 fixed)"
      ((JuliaBase.F64.sum w - 2).abs ≤ 1e-14)
  -- 5. Lagrange and sinc
  let lj ← jField g "lagrange"
  let xa := Axis.colon 0 0.25 1
  let xs := xa.toFloatArray
  let ys : FloatArray := ⟨xs.data.map fun x => x * x * x - x⟩
  checkFloats "spectral lagrangeweights" (lagrangeweights xs) (← fl lj "w")
  checkFloats "spectral lagrangepolynomial" (lagrangepolynomial xs ys ⟨#[0.3, 0.5, -0.1, 1.2, 0.25]⟩)
    (← fl lj "at")
  checkRel "spectral resample_lagrange 9" (lagrangepolynomial xs ys (xa.resample 9).toFloatArray)
    (← fl lj "resample9") 1e-14
  checkFloats "spectral rootspolynomial" ⟨#[rootspolynomial xs 0.3]⟩ ⟨#[← gFloat (← jField lj "roots03")]⟩
  checkRel "spectral resample_sinc 9" (resampleSinc xa ys 9).2 (← fl lj "sinc9") 1e-14
  let lr ← jField g "lagrange_rand"
  let xr ← fl lr "x"
  let yr ← fl lr "y"
  checkFloats "spectral lagrangeweights (random nodes)" (lagrangeweights xr) (← fl lr "w")
  checkFloats "spectral lagrangepolynomial (random nodes)" (lagrangepolynomial xr yr ⟨#[0.1, 0.77, 1.5, 2.1]⟩)
    (← fl lr "at")
  -- 6. Fourier series
  let sj ← jField g "series"
  let ax := Axis.colon 0 (piF / 64) piF
  let xx := ax.toFloatArray
  let gcos : FloatArray := ⟨(Array.range ax.length).map fun i =>
    F64.cos ((ax.scale 2).getD ax |>.get i) + 0.5⟩
  checkRel "spectral FourierCosine coefficients" (seriesCoefficients FourierCosine xx gcos 5) (← fl sj "cos") 1e-12
  let gsin : FloatArray := ⟨(Array.range ax.length).map fun i => F64.sin ((ax.scale 3).getD ax |>.get i)⟩
  checkRel "spectral FourierSine coefficients" (seriesCoefficients FourierSine xx gsin 5) (← fl sj "sin") 1e-12
  let q := Axis.colon 0 0.25 1
  checkFloats "spectral FourierCosine(2, t)" ⟨(Array.range q.length).map fun i => FourierCosine.f 2 (q.get i)⟩
    (← fl sj "cos2") libm

end Tests.CartanTests.SpectralTests
