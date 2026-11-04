import Cartan.Spectral.FFT

/-!
# FFTs of arrays of elements (Grassmann.jl's AbstractFFTs glue)

Grassmann.jl (`src/Grassmann.jl:350-358`) makes AbstractFFTs accept arrays of algebra
elements. It does this by reading each element as a complex number:

* a `Couple{V,B}` `a + bB` is `a + bi` (the transform then acts on the plane `⟨1, B⟩`);
* a `Phasor` goes through `complexify` to a `Couple`;
* grade-0 elements (scalars) go through `Real`.

The transforms are FFTW's (`Cartan.Spectral.FFT`). Every element must have the same blade
`B`, as Julia's array element type `Couple{V,B}` guarantees. A mixed array is an error
here (`none`), where Julia would fail to build the array. Because the transforms are
linear in `(re, im)`, the metric of `B` (`B² = −1`, `+1` or `0`) does not enter.
Julia's glue ignores the metric in the same way.
-/

namespace Cartan.Spectral

open Grassmann

namespace Elements

variable {V : TensorBundle}

/-- The common blade of an array of couples (`none` if two differ). An empty array has
blade `0`. -/
def commonBlade (zs : Array (Couple V Float)) : Option UInt64 :=
  match zs[0]? with
  | none => some 0
  | some z => if zs.all (·.bits == z.bits) then some z.bits else none

/-- The couples as an interleaved complex vector. -/
def toCVec (zs : Array (Couple V Float)) : CVec := Id.run do
  let mut c := FloatArray.emptyWithCapacity (2 * zs.size)
  for z in zs do
    c := (c.push z.re).push z.im
  return c

/-- A complex vector as couples of blade `B`. -/
def ofCVec (B : UInt64) (c : CVec) : Array (Couple V Float) :=
  (Array.range c.len).map fun k => ⟨B, c.re k, c.im k⟩

/-- Lift a complex-vector transform to arrays of couples of one blade. -/
@[inline] def lift (f : CVec → CVec) (zs : Array (Couple V Float)) : Option (Array (Couple V Float)) :=
  (commonBlade zs).map fun B => ofCVec B (f (toCVec zs))

/-- `fft` of an array of couples `aₖ + bₖB` (FFTW's sign `e^{−2πi jk/N}`, unnormalized). -/
def fft (zs : Array (Couple V Float)) : Option (Array (Couple V Float)) := lift Spectral.fft zs

/-- `bfft` (the unnormalized backward transform). -/
def bfft (zs : Array (Couple V Float)) : Option (Array (Couple V Float)) := lift Spectral.bfft zs

/-- `ifft = bfft / N`. -/
def ifft (zs : Array (Couple V Float)) : Option (Array (Couple V Float)) := lift Spectral.ifft zs

/-- `fft` of an array of phasors, through `complexify` (Julia's glue). -/
def fftPhasors (ps : Array (Phasor V Float)) : Option (Array (Couple V Float)) :=
  fft (ps.map Phasor.complexify)

/-- `ifft` of an array of phasors, through `complexify`. -/
def ifftPhasors (ps : Array (Phasor V Float)) : Option (Array (Couple V Float)) :=
  ifft (ps.map Phasor.complexify)

/-- `fft` of grade-0 elements (Julia's `Real` conversion): the complex spectrum of the real
values, as couples of a chosen blade `B` (the plane `⟨1, B⟩` the spectrum lives in). -/
def fftScalars (B : UInt64) (xs : FloatArray) : Array (Couple V Float) :=
  ofCVec B (Spectral.fft (CVec.ofReal xs))

/-- `rfft` of grade-0 elements: the first `N÷2 + 1` bins, as couples of blade `B`. -/
def rfftScalars (B : UInt64) (xs : FloatArray) : Array (Couple V Float) :=
  ofCVec B (Spectral.rfft xs)

end Elements

end Cartan.Spectral
