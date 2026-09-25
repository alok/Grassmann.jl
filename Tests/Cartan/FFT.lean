import Tests.Cartan.Solve
import Cartan.Spectral.FFT

/-!
# FFT against FFTW (`oracle/golden/cartan/element/fft.json`)

Generator `oracle/cartan/element/fft.jl` (FFTW 1.x in a copy of the oracle environment). For every
length (radix 2, mixed radix `3·5`, `2²·3`, `3⁵`, `10²`, and the Bluestein primes 127, and 31, 17
by mixed radix), random real and complex inputs: `fft`, `bfft`, `ifft`, `rfft`, `irfft`,
`brfft`, all eleven `r2r` kinds and `dct`/`idct`, compared to `1e-13` of the largest coefficient
(FFTW's factorizations round differently).
-/

open Lean Tests.Small Cartan JuliaBase Cartan.Spectral
open Tests.CartanTests.SolveTests (checkRel)

namespace Tests.CartanTests.FFTTests

/-- Run the FFT checks. -/
def run : TestM Unit := do
  let g ← load "element/fft"
  for c in ← jArr (← jField g "cases") do
    let N ← jNat (← jField c "N")
    let x ← gFloats (← jField c "x")
    let y ← gFloats (← jField c "y")
    let z := CVec.ofReIm x y
    let tol := 1e-13
    checkRel s!"fft N={N}" (fft z) (← gFloats (← jField c "fft")) tol
    checkRel s!"bfft N={N}" (bfft z) (← gFloats (← jField c "bfft")) tol
    checkRel s!"ifft N={N}" (ifft z) (← gFloats (← jField c "ifft")) tol
    checkRel s!"rfft N={N}" (rfft x) (← gFloats (← jField c "rfft")) tol
    checkRel s!"irfft N={N}" (irfft (rfft x) N) (← gFloats (← jField c "irfft")) tol
    checkRel s!"brfft N={N}" (brfft (rfft y) N) (← gFloats (← jField c "brfft")) tol
    checkRel s!"dct N={N}" (dct x) (← gFloats (← jField c "dct")) tol
    checkRel s!"idct N={N}" (idct x) (← gFloats (← jField c "idct")) tol
    let r ← jField c "r2r"
    for k in [0:11] do
      match r.getObjVal? (toString k), R2RKind.ofCode? k with
      | .ok j, some kind =>
        if !isErr j then
          checkRel s!"r2r {repr kind} N={N}" (r2r x kind) (← gFloats j) tol
      | _, _ => pure ()

end Tests.CartanTests.FFTTests
