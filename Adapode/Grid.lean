import Cartan.Spectral

/-!
# Spectral PDE solvers on grids (Adapode.jl `src/grid.jl:214-330`, `ext/FFTWExt.jl`)

Port notes: `docs/port-notes/adapode.md` §2.7. Every solver diagonalises a constant-coefficient
operator with a fast transform, multiplies by its symbol and transforms back:

| boundary | transform | frequencies (axis `d`, `L = x[end] − x[1]`) |
|---|---|---|
| periodic | `rfft` on axis 1, `fft` on the others | `k·2π/L` (`k ≤ N/2` on axis 1, signed on the others) |
| Neumann | orthonormal `dct`/`idct` (DCT-II/III) | `k·π/L`, `k = 0 … N−1` |
| Dirichlet | `r2r(·, RODFT10)/Π 2N`, then `RODFT01` | `k·π/L`, `k = 1 … N` |

The symbols (`grid.jl:214-221`) are functions of `|k|²`: `heat` `e^{−t|k|²}`, `riesz`
`e^{−t|k|^s}`, `biharmonic` `e^{−t|k|⁴}`, `restwave` `cos(t|k|)`, `wave` `sin(t|k|)/|k|` and
`schrodinger` `e^{−it|k|²/2}`. Data are column-major arrays (axis 1 fastest, Julia's layout) over
the product of `axes`; a time series stores the slices one after another (time is the last
dimension, `size(u0)..., length(t)`).

The frequency step is Julia's `2π/(x[end]−x[1])` (the closed interval, Cartan B20), so a function
sampled at both ends of its period, such as `sin(πx)` on `-1:0.01:1`, decays at the rate of its own
period.

**Julia defects fixed** (`oracle/adapode/defects.toml`):
* **B18** multi-dimensional periodic solves use the non-negative `fftspace` on axes 2… and
  `rfftspace(x.v[2])` on axis 1, and the Schrödinger solver uses non-negative frequencies: here the
  `fft` axes carry signed frequencies and axis 1 its own `rfftspace`;
* **B19** `biharmonicneumann`/`biharmonicdirichlet` are undefined and `fullwaveneumann` is not
  imported: all are defined here;
* the time series store `u0` itself as their first slice whatever `t[1]` is: here slice `i` is the
  solution at `t[i]` (`u0` exactly when `t[i] = 0`, as in Julia).
-/

namespace Adapode.Grid

open Cartan Cartan.Spectral JuliaBase

/-! ## Symbols (`grid.jl:214-221`), as functions of `|k|²` -/

/-- `restwavemultiplier(k, t) = cos(t|k|)`. -/
@[inline] def restwaveMultiplier (k2 t : Float) : Float := F64.cos (t * Float.sqrt k2)

/-- `wavemultiplier(k, t) = sin(t|k|)/|k|` (`NaN` at `k = 0`; the solvers replace it). -/
@[inline] def waveMultiplier (k2 t : Float) : Float :=
  let a := Float.sqrt k2
  F64.sin (t * a) / a

/-- `heatmultiplier(k, t) = exp(−t|k|²)`. -/
@[inline] def heatMultiplier (k2 t : Float) : Float := F64.exp (-t * k2)

/-- `rieszmultiplier(k, t, s) = exp(−t (|k|²)^{s/2})`. -/
@[inline] def rieszMultiplier (k2 t : Float) (s : Float := 2) : Float :=
  F64.exp (-t * Float.pow k2 (s / 2))

/-- `biharmonicmultiplier(k, t) = exp(−t|k|⁴)`. -/
@[inline] def biharmonicMultiplier (k2 t : Float) : Float := F64.exp (-t * (k2 * k2))

/-- `multiplierstep(mult, k, t) = (mult(k, t) − 1)/t`. -/
@[inline] def multiplierStep (mult : Float → Float → Float) (k2 t : Float) : Float :=
  (mult k2 t - 1) / t

/-! ## Column-major line transforms -/

/-- The product of a slice of the dimensions. -/
@[inline] def prodDims (dims : Array Nat) (a b : Nat) : Nat :=
  (dims.extract a b).foldl (· * ·) 1

/-- Apply `f` to every line along axis `d` of a column-major array of elements of `w` floats
(`w = 2` for interleaved complex data). `f` maps a line of `dims[d]` elements to `m` elements of
`w'` floats; the result has `dims[d]` replaced by `m`. -/
def mapLines (dims : Array Nat) (d w w' m : Nat) (f : FloatArray → FloatArray) (x : FloatArray) :
    FloatArray := Id.run do
  let n := dims[d]!
  let lo := prodDims dims 0 d
  let hi := prodDims dims (d + 1) dims.size
  let mut out : FloatArray := ⟨Array.replicate (lo * m * hi * w') 0⟩
  for h in [0:hi] do
    for l in [0:lo] do
      let mut line : FloatArray := FloatArray.emptyWithCapacity (n * w)
      for j in [0:n] do
        let src := (l + lo * (j + n * h)) * w
        for c in [0:w] do line := line.push (x.get! (src + c))
      let y := f line
      for j in [0:m] do
        let dst := (l + lo * (j + m * h)) * w'
        for c in [0:w'] do out := out.set! (dst + c) (y.get! (j * w' + c))
  return out

/-- A real transform `f` along every axis. -/
def alongAll (dims : Array Nat) (f : FloatArray → FloatArray) (x : FloatArray) : FloatArray :=
  (List.range dims.size).foldl (fun y d => mapLines dims d 1 1 dims[d]! f y) x

/-- The spectral shape of `rfftN`: axis 1 halved. -/
def rfftDims (dims : Array Nat) : Array Nat :=
  if dims.isEmpty then dims else dims.set! 0 (dims[0]! / 2 + 1)

/-- The multi-dimensional `rfft`: `rfft` along axis 1, then `fft` along the others. -/
def rfftN (dims : Array Nat) (x : FloatArray) : CVec :=
  let sd := rfftDims dims
  let y := mapLines dims 0 1 2 sd[0]! Spectral.rfft x
  (List.range (dims.size - 1)).foldl (fun y d => mapLines sd (d + 1) 2 2 sd[d + 1]! Spectral.fft y) y

/-- The inverse of `rfftN` (normalized). -/
def irfftN (dims : Array Nat) (X : CVec) : FloatArray :=
  let sd := rfftDims dims
  let Y := (List.range (dims.size - 1)).foldl
    (fun y d => mapLines sd (d + 1) 2 2 sd[d + 1]! Spectral.ifft y) X
  mapLines sd 0 2 1 dims[0]! (fun z => Spectral.irfft z dims[0]!) Y

/-- The multi-dimensional complex `fft`. -/
def fftN (dims : Array Nat) (z : CVec) : CVec :=
  (List.range dims.size).foldl (fun y d => mapLines dims d 2 2 dims[d]! Spectral.fft y) z

/-- The multi-dimensional complex `ifft`. -/
def ifftN (dims : Array Nat) (z : CVec) : CVec :=
  (List.range dims.size).foldl (fun y d => mapLines dims d 2 2 dims[d]! Spectral.ifft y) z

/-- FFTW.jl `dct` of an array (orthonormal DCT-II along every axis). -/
def dctN (dims : Array Nat) (x : FloatArray) : FloatArray := alongAll dims Spectral.dct x

/-- FFTW.jl `idct` of an array. -/
def idctN (dims : Array Nat) (x : FloatArray) : FloatArray := alongAll dims Spectral.idct x

/-- FFTW `r2r(x, kind)` of an array (the same kind along every axis). -/
def r2rN (dims : Array Nat) (x : FloatArray) (kind : R2RKind) : FloatArray :=
  alongAll dims (Spectral.r2r · kind) x

/-! ## Frequencies -/

/-- `|k|² = Σ_d k_d[i_d]²` over the column-major product of the frequency axes. -/
def normSq (freqs : Array FloatArray) : FloatArray := Id.run do
  let dims := freqs.map (·.size)
  let total := dims.foldl (· * ·) 1
  let mut out : FloatArray := FloatArray.emptyWithCapacity total
  for q in [0:total] do
    let mut r := q
    let mut s := 0.0
    for f in freqs do
      let n := f.size
      let k := f.get! (r % n)
      s := s + k * k
      r := r / n
    out := out.push s
  return out

/-- Signed frequencies from the non-negative `fftspace` values: bin `k > N/2` is `−f[N−k]`. -/
def signedFreqs (f : FloatArray) : FloatArray :=
  let N := f.size
  ⟨(Array.range N).map fun k => if 2 * k > N then -(f.get! (N - k)) else f.get! k⟩

/-- The periodic frequencies: `rfftspace` on axis 1, signed `fftspace` on the others (B18). -/
def periodicFreqs (axes : Array Axis) : Array FloatArray :=
  (Array.range axes.size).map fun d =>
    let a := axes[d]!
    if d == 0 then rfftFreqs a.length (fftOmega a)
    else signedFreqs (fftFreqs a.length (fftOmega a))

/-- The signed `fft` frequencies of every axis (the Schrödinger solver, B18). -/
def fullFreqs (axes : Array Axis) : Array FloatArray :=
  axes.map fun a => signedFreqs (fftFreqs a.length (fftOmega a))

/-- The Neumann (DCT) frequencies, Julia `r2rspace(x)`: `k·π/L`. -/
def neumannFreqs (axes : Array Axis) : Array FloatArray :=
  axes.map fun a => fftFreqs a.length (piF / (a.last - a.first))

/-- The Dirichlet (DST) frequencies, Julia `r2rspace(x, RODFT10)`: `(k+1)·π/L`. -/
def dirichletFreqs (axes : Array Axis) : Array FloatArray :=
  axes.map fun a => r2rFreqs a.length .RODFT10 ((a.last - a.first) / piF)

/-! ## Generic solvers -/

/-- `Z .* m` for complex `Z` and a real symbol `m`. -/
def scaleC (m : FloatArray) (Z : CVec) : CVec :=
  ⟨(Array.range Z.size).map fun q => Z.get! q * m.get! (q / 2)⟩

/-- `x .* m` elementwise. -/
def scaleR (m x : FloatArray) : FloatArray :=
  ⟨(Array.range x.size).map fun q => x.get! q * m.get! q⟩

/-- The symbol evaluated on `|k|²`. -/
@[inline] def symbol (k2 : FloatArray) (mult : Float → Float) : FloatArray := ⟨k2.data.map mult⟩

/-- The wave symbol `sin(t|k|)/|k|` with the value `dc` at `k = 0` (`wm[1] = 0` or `t`). -/
def waveSymbol (k2 : FloatArray) (t dc : Float) : FloatArray :=
  ⟨k2.data.map fun s => if s == 0 then dc else waveMultiplier s t⟩

/-- Julia `irfft(rfft(u0) .* mult.(k))`. -/
def periodic (axes : Array Axis) (mult : Float → Float) (u0 : FloatArray) : FloatArray :=
  let dims := axes.map (·.length)
  irfftN dims (scaleC (symbol (normSq (periodicFreqs axes)) mult) (rfftN dims u0))

/-- Julia `idct(dct(u0) .* mult.(k))`. -/
def neumann (axes : Array Axis) (mult : Float → Float) (u0 : FloatArray) : FloatArray :=
  let dims := axes.map (·.length)
  idctN dims (scaleR (symbol (normSq (neumannFreqs axes)) mult) (dctN dims u0))

/-- `r2r(u, RODFT10)/Π(2 size(u))`. -/
def dstN (dims : Array Nat) (u : FloatArray) : FloatArray :=
  let c := 1 / dims.foldl (fun p n => p * (2 * n.toUInt64.toFloat)) 1
  ⟨(r2rN dims u .RODFT10).data.map (· * c)⟩

/-- Julia `r2r(r2r(u0, RODFT10)/Π(2 size(u0)) .* mult.(ω), RODFT01)`. -/
def dirichlet (axes : Array Axis) (mult : Float → Float) (u0 : FloatArray) : FloatArray :=
  let dims := axes.map (·.length)
  r2rN dims (scaleR (symbol (normSq (dirichletFreqs axes)) mult) (dstN dims u0)) .RODFT01

/-! ## Heat, Riesz, biharmonic and rest-wave solvers -/

/-- `heatperiodic(u0, t)`: `u_t = Δu` on the periodic grid. -/
def heatPeriodic (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  periodic axes (heatMultiplier · t) u0
/-- `heatneumann(u0, t)`. -/
def heatNeumann (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  neumann axes (heatMultiplier · t) u0
/-- `heatdirichlet(u0, t)`. -/
def heatDirichlet (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  dirichlet axes (heatMultiplier · t) u0

/-- `rieszperiodic(u0, t, s)`: `u_t = −(−Δ)^{s/2} u`. -/
def rieszPeriodic (axes : Array Axis) (u0 : FloatArray) (t : Float) (s : Float := 2) : FloatArray :=
  periodic axes (rieszMultiplier · t s) u0
/-- `rieszneumann(u0, t, s)`. -/
def rieszNeumann (axes : Array Axis) (u0 : FloatArray) (t : Float) (s : Float := 2) : FloatArray :=
  neumann axes (rieszMultiplier · t s) u0
/-- `rieszdirichlet(u0, t, s)`. -/
def rieszDirichlet (axes : Array Axis) (u0 : FloatArray) (t : Float) (s : Float := 2) : FloatArray :=
  dirichlet axes (rieszMultiplier · t s) u0

/-- `biharmonicperiodic(u0, t)`: `u_t = −Δ²u`. -/
def biharmonicPeriodic (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  periodic axes (biharmonicMultiplier · t) u0
/-- `biharmonicneumann(u0, t)` (undefined in Julia, B19). -/
def biharmonicNeumann (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  neumann axes (biharmonicMultiplier · t) u0
/-- `biharmonicdirichlet(u0, t)` (undefined in Julia, B19). -/
def biharmonicDirichlet (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  dirichlet axes (biharmonicMultiplier · t) u0

/-- `restwaveperiodic(u0, t)`: the wave equation released from rest (`u_t(0) = 0`). -/
def restwavePeriodic (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  periodic axes (restwaveMultiplier · t) u0
/-- `restwaveneumann(u0, t)`. -/
def restwaveNeumann (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  neumann axes (restwaveMultiplier · t) u0
/-- `restwavedirichlet(u0, t)`. -/
def restwaveDirichlet (axes : Array Axis) (u0 : FloatArray) (t : Float) : FloatArray :=
  dirichlet axes (restwaveMultiplier · t) u0

/-! ## Wave solvers with an initial velocity -/

/-- Julia `irfft(rfft(u0) .* cos + rfft(u1) .* wm)` with `wm[k=0] = dc`. -/
def wavePeriodicWith (axes : Array Axis) (u0 u1 : FloatArray) (t dc : Float) : FloatArray :=
  let dims := axes.map (·.length)
  let k2 := normSq (periodicFreqs axes)
  let A := scaleC (symbol k2 (restwaveMultiplier · t)) (rfftN dims u0)
  let B := scaleC (waveSymbol k2 t dc) (rfftN dims u1)
  irfftN dims ⟨(Array.range A.size).map fun q => A.get! q + B.get! q⟩

/-- `waveperiodic(u0, u1, t)`: the mean of `u1` is dropped (`wm[1] = 0`). -/
def wavePeriodic (axes : Array Axis) (u0 u1 : FloatArray) (t : Float) : FloatArray :=
  wavePeriodicWith axes u0 u1 t 0

/-- `fullwaveperiodic(u0, u1, t)`: the mean of `u1` drifts (`wm[1] = t`). -/
def fullwavePeriodic (axes : Array Axis) (u0 u1 : FloatArray) (t : Float) : FloatArray :=
  wavePeriodicWith axes u0 u1 t t

/-- Julia `idct(dct(u0) .* cos + dct(u1) .* wm)` with `wm[k=0] = dc`. -/
def waveNeumannWith (axes : Array Axis) (u0 u1 : FloatArray) (t dc : Float) : FloatArray :=
  let dims := axes.map (·.length)
  let k2 := normSq (neumannFreqs axes)
  let A := scaleR (symbol k2 (restwaveMultiplier · t)) (dctN dims u0)
  let B := scaleR (waveSymbol k2 t dc) (dctN dims u1)
  idctN dims ⟨(Array.range A.size).map fun q => A.get! q + B.get! q⟩

/-- `waveneumann(u0, u1, t)`. -/
def waveNeumann (axes : Array Axis) (u0 u1 : FloatArray) (t : Float) : FloatArray :=
  waveNeumannWith axes u0 u1 t 0

/-- `fullwaveneumann(u0, u1, t)` (unreachable in Julia, B19). -/
def fullwaveNeumann (axes : Array Axis) (u0 u1 : FloatArray) (t : Float) : FloatArray :=
  waveNeumannWith axes u0 u1 t t

/-- `wavedirichlet(u0, u1, t)`: the sum of the `cos` solution of `u0` and the `sin/k` solution
of `u1`. -/
def waveDirichlet (axes : Array Axis) (u0 u1 : FloatArray) (t : Float) : FloatArray :=
  let dims := axes.map (·.length)
  let k2 := normSq (dirichletFreqs axes)
  let A := scaleR (symbol k2 (restwaveMultiplier · t)) (dstN dims u0)
  let B := scaleR (symbol k2 (waveMultiplier · t)) (dstN dims u1)
  r2rN dims ⟨(Array.range A.size).map fun q => A.get! q + B.get! q⟩ .RODFT01

/-! ## Schrödinger -/

/-- `schrodingerperiodic(u0, t)` of complex data: `ifft(fft(u0) .* exp(−it|k|²/2))`, with signed
frequencies on every axis (B18). -/
def schrodingerPeriodicC (axes : Array Axis) (u0 : CVec) (t : Float) : CVec := Id.run do
  let dims := axes.map (·.length)
  let k2 := normSq (fullFreqs axes)
  let Z := fftN dims u0
  let mut W : CVec := CVec.zeros k2.size
  for q in [0:k2.size] do
    let (s, c) := F64.sincos (-(t * k2.get! q) / 2)
    let zr := Z.get! (2 * q)
    let zi := Z.get! (2 * q + 1)
    W := (W.set! (2 * q) (zr * c - zi * s)).set! (2 * q + 1) (zr * s + zi * c)
  return ifftN dims W

/-- `schrodingerperiodic(u0, t)` of real data. -/
def schrodingerPeriodic (axes : Array Axis) (u0 : FloatArray) (t : Float) : CVec :=
  schrodingerPeriodicC axes (CVec.ofReal u0) t

/-! ## Time series (`grid.jl:256-330`, FFTWExt 33-87) -/

/-- The solutions at the times `ts`, slice after slice (time is the last dimension); a slice at
`t = 0` is `u0` itself, as in Julia. -/
def series (u0 : FloatArray) (solve : Float → FloatArray) (ts : Array Float) : FloatArray :=
  ts.foldl (fun acc t => (if t == 0 then u0 else solve t).data.foldl FloatArray.push acc)
    (FloatArray.emptyWithCapacity (u0.size * ts.size))

/-- The `i`-th slice of a series of `n`-point solutions. -/
def slice (out : FloatArray) (n i : Nat) : FloatArray := ⟨out.data.extract (i * n) ((i + 1) * n)⟩

/-! ## Fields over one axis -/

namespace Field

variable {a : Axis}

/-- The field over `a` with values `x`. -/
@[inline] def mk' (x : FloatArray) : TensorField (GridBundle.ofAxis a) Float := TensorField.ofReals _ x

/-- `heatperiodic(u0, t)` of a field. -/
def heatPeriodic (u0 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.heatPeriodic #[a] u0.data t)
/-- `heatneumann(u0, t)` of a field. -/
def heatNeumann (u0 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.heatNeumann #[a] u0.data t)
/-- `heatdirichlet(u0, t)` of a field. -/
def heatDirichlet (u0 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.heatDirichlet #[a] u0.data t)
/-- `waveperiodic(u0, u1, t)` of fields. -/
def wavePeriodic (u0 u1 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.wavePeriodic #[a] u0.data u1.data t)
/-- `waveneumann(u0, u1, t)` of fields. -/
def waveNeumann (u0 u1 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.waveNeumann #[a] u0.data u1.data t)
/-- `wavedirichlet(u0, u1, t)` of fields. -/
def waveDirichlet (u0 u1 : TensorField (GridBundle.ofAxis a) Float) (t : Float) :
    TensorField (GridBundle.ofAxis a) Float := mk' (Grid.waveDirichlet #[a] u0.data u1.data t)

end Field

end Adapode.Grid
