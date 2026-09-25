import Cartan.Flat

/-!
# Fast Fourier transforms (FFTW's conventions)

Cartan's spectral tools (`src/spectral.jl`, `ext/FFTWExt.jl`) call FFTW through AbstractFFTs;
this is a dependency-free replacement with FFTW's definitions:

* `fft`: `X_k = Σ_j x_j e^{−2πi jk/N}` (unnormalized); `bfft`: the same with `e^{+…}`;
  `ifft = bfft / N`;
* `rfft`: the first `N÷2 + 1` bins of the FFT of a real vector; `irfft(X, N)`, `brfft(X, N)`: the
  real inverse of a Hermitian half-spectrum of a length-`N` signal;
* the real-to-real kinds `r2r(x, kind)` (FFTW's codes `R2HC=0 … RODFT11=10`), unnormalized as in
  FFTW, and FFTW.jl's orthonormal `dct`/`idct` (DCT-II/III scaled by `√(2/N)`, `√(1/N)` at `0`).

**Algorithm.** Complex data are interleaved `(re₀, im₀, re₁, im₁, …)` in a `FloatArray`. Powers
of two run the iterative radix-2 Cooley–Tukey transform (bit reversal, then butterflies with a
twiddle table); other lengths the recursive mixed-radix decimation in time over their prime
factors (generic `p`-point butterflies); lengths with a prime factor above 64 use Bluestein's
chirp-z algorithm (a power-of-two convolution). Twiddles `e^{−2πik/N}` are computed with Julia's
own `sincos` of `2πk/N` reduced to the first octant, and cached per length.

**Accuracy.** FFTW uses different factorizations and codelets, so results agree with Julia's to
rounding (the tests compare to `1e-13` of the largest coefficient), not bit for bit; the error
grows like `ε log N` (radix 2) and `ε N^{1/2}`-ish at worst for Bluestein.
-/

namespace Cartan.Spectral

open JuliaBase

/-- Complex vectors as interleaved `(re, im)` pairs. -/
abbrev CVec := FloatArray

namespace CVec

/-- Length (number of complex entries). -/
@[inline] def len (z : CVec) : Nat := z.size / 2

/-- Real part of entry `k`. -/
@[inline] def re (z : CVec) (k : Nat) : Float := z.get! (2 * k)

/-- Imaginary part of entry `k`. -/
@[inline] def im (z : CVec) (k : Nat) : Float := z.get! (2 * k + 1)

/-- `n` zeros. -/
def zeros (n : Nat) : CVec := ⟨Array.replicate (2 * n) 0⟩

/-- A real vector as a complex one. -/
def ofReal (x : FloatArray) : CVec := Id.run do
  let mut z := FloatArray.emptyWithCapacity (2 * x.size)
  for i in [0:x.size] do
    z := (z.push (x.get! i)).push 0
  return z

/-- From `(re, im)` arrays. -/
def ofReIm (r i : FloatArray) : CVec := Id.run do
  let mut z := FloatArray.emptyWithCapacity (2 * r.size)
  for k in [0:r.size] do
    z := (z.push (r.get! k)).push (i.get! k)
  return z

/-- The real parts. -/
def realPart (z : CVec) : FloatArray := ⟨(Array.range z.len).map z.re⟩

/-- The imaginary parts. -/
def imagPart (z : CVec) : FloatArray := ⟨(Array.range z.len).map z.im⟩

/-- Entrywise complex conjugate. -/
def conj (z : CVec) : CVec := ⟨(Array.range z.size).map fun q => if q % 2 == 1 then -z.get! q else z.get! q⟩

/-- Scale by a real. -/
def scale (s : Float) (z : CVec) : CVec := ⟨z.data.map (· * s)⟩

/-- Entrywise product. -/
def mul (a b : CVec) : CVec := Id.run do
  let n := a.len
  let mut z := FloatArray.emptyWithCapacity (2 * n)
  for k in [0:n] do
    let ar := a.re k
    let ai := a.im k
    let br := b.re k
    let bi := b.im k
    z := (z.push (ar * br - ai * bi)).push (ar * bi + ai * br)
  return z

end CVec

/-! ## Twiddles -/

/-- `(cos(πa/b), sin(πa/b))` with Julia's `sincospi`, the argument reduced exactly modulo `2` on
the integers first (so a table of roots of unity is accurate to an ulp or two for every `N`). -/
def cossinpiRat (a b : Nat) : Float × Float :=
  let a := a % (2 * b)
  let (s, c) := JuliaBase.F64.sincospi (a.toUInt64.toFloat / b.toUInt64.toFloat)
  (c, s)

/-- `(cos θ, sin θ)` of `θ = 2πk/N`. -/
def unitRoot (k N : Nat) : Float × Float := cossinpiRat (2 * k) N

/-- The table `e^{−2πik/N}`, `k < N`, as interleaved `(cos, −sin)`. -/
def twiddleTable (N : Nat) : CVec := Id.run do
  let mut z := FloatArray.emptyWithCapacity (2 * N)
  for k in [0:N] do
    let (c, s) := unitRoot k N
    z := (z.push c).push (-s)
  return z

private unsafe def twiddleCacheImpl : IO.Ref (Std.HashMap Nat CVec) := unsafeBaseIO (IO.mkRef {})

/-- Cached twiddle tables. -/
@[implemented_by twiddleCacheImpl]
private opaque twiddleCache : IO.Ref (Std.HashMap Nat CVec)

private unsafe def twiddlesImpl (N : Nat) : CVec := unsafeBaseIO do
  match (← twiddleCache.get)[N]? with
  | some t => return t
  | none =>
    let t := twiddleTable N
    if N ≤ 1 <<< 22 then twiddleCache.modify (·.insert N t)
    return t

/-- `e^{−2πik/N}` for `k < N` (logically `twiddleTable N`; cached per length). -/
@[implemented_by twiddlesImpl]
def twiddles (N : Nat) : CVec := twiddleTable N

/-! ## Transforms -/

/-- Whether `n` is a power of two (`n ≥ 1`). -/
def isPow2 (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- The smallest prime factor of `n ≥ 2`. -/
def smallestFactor (n : Nat) : Nat := Id.run do
  if n % 2 == 0 then return 2
  let mut p := 3
  while p * p ≤ n do
    if n % p == 0 then return p
    p := p + 2
  return n

/-- The largest prime factor of `n` (`1` for `n ≤ 1`). -/
def largestFactor (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut best := 1
  let mut p := 2
  while p * p ≤ m do
    while m % p == 0 do
      best := p
      m := m / p
    p := p + 1
  return if m > 1 then m else best

/-- The bit reversal of `i` over `bits` bits. -/
def bitrev (i bits : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := i
  for _ in [0:bits] do
    r := 2 * r + x % 2
    x := x / 2
  return r

/-- Iterative radix-2 FFT of a power-of-two length, `sign = -1` forward, `+1` backward. -/
def fftPow2 (z0 : CVec) (sign : Float) : CVec := Id.run do
  let n := z0.len
  if n ≤ 1 then return z0
  let bits := Nat.log2 n
  let tw := twiddles n
  let mut z := z0
  for i in [0:n] do
    let j := bitrev i bits
    if i < j then
      let ar := z.get! (2 * i); let ai := z.get! (2 * i + 1)
      let br := z.get! (2 * j); let bi := z.get! (2 * j + 1)
      z := (((z.set! (2 * i) br).set! (2 * i + 1) bi).set! (2 * j) ar).set! (2 * j + 1) ai
  let mut half := 1
  while half < n do
    let len := 2 * half
    let step := n / len
    let mut s := 0
    while s < n do
      for k in [0:half] do
        let wr := tw.get! (2 * (k * step))
        let wi := sign * -(tw.get! (2 * (k * step) + 1))
        -- tw holds (cos, −sin); w = cos + i·sign·sin
        let a := s + k
        let b := a + half
        let br := z.get! (2 * b); let bi := z.get! (2 * b + 1)
        let tr := br * wr - bi * wi
        let ti := br * wi + bi * wr
        let ar := z.get! (2 * a); let ai := z.get! (2 * a + 1)
        z := (((z.set! (2 * a) (ar + tr)).set! (2 * a + 1) (ai + ti)).set! (2 * b) (ar - tr)).set! (2 * b + 1) (ai - ti)
      s := s + len
    half := len
  return z

mutual

/-- The DFT of a length with no prime factor above 64 (mixed-radix decimation in time), or
Bluestein otherwise. `sign = -1` forward, `+1` backward. -/
partial def dft (z : CVec) (sign : Float) : CVec :=
  let n := z.len
  if n ≤ 1 then z
  else if isPow2 n then fftPow2 z sign
  else if largestFactor n > 64 then bluestein z sign
  else mixedRadix z sign

/-- One level of mixed-radix decimation in time: `n = p·m`, `X_k = Σ_r W^{rk} Y_r[k mod m]`. -/
partial def mixedRadix (z : CVec) (sign : Float) : CVec := Id.run do
  let n := z.len
  let p := smallestFactor n
  let m := n / p
  let tw := twiddles n
  -- sub-transforms of the decimated sequences x_{r + p j}
  let subs : Array CVec := (Array.range p).map fun r =>
    dft ⟨(Array.range (2 * m)).map fun q => z.get! (2 * (r + p * (q / 2)) + q % 2)⟩ sign
  let mut out := FloatArray.emptyWithCapacity (2 * n)
  for k in [0:n] do
    let km := k % m
    let mut sr := 0.0
    let mut si := 0.0
    for r in [0:p] do
      let y := subs[r]!
      let yr := y.get! (2 * km)
      let yi := y.get! (2 * km + 1)
      let e := (r * k) % n
      let wr := tw.get! (2 * e)
      let wi := sign * -(tw.get! (2 * e + 1))
      sr := sr + (yr * wr - yi * wi)
      si := si + (yr * wi + yi * wr)
    out := (out.push sr).push si
  return out

/-- Bluestein's chirp-z DFT: `X_k = c̄_k Σ_j (x_j c̄_j) c_{k−j}` with `c_j = e^{iπ j²/n}` (sign
convention folded in), a power-of-two circular convolution of length `M ≥ 2n − 1`. -/
partial def bluestein (z : CVec) (sign : Float) : CVec := Id.run do
  let n := z.len
  let mut M := 1
  while M < 2 * n - 1 do M := 2 * M
  -- chirp w_j = e^{sign·iπ j²/n}, j² reduced mod 2n
  let chirp : CVec := Id.run do
    let mut c := FloatArray.emptyWithCapacity (2 * n)
    for j in [0:n] do
      let e := (j * j) % (2 * n)
      let (cs, sn) := cossinpiRat e n
      c := (c.push cs).push (sign * sn)
    return c
  let mut a := CVec.zeros M
  for j in [0:n] do
    -- a_j = x_j · w_j
    let xr := z.re j; let xi := z.im j
    let wr := chirp.re j; let wi := chirp.im j
    a := (a.set! (2 * j) (xr * wr - xi * wi)).set! (2 * j + 1) (xr * wi + xi * wr)
  let mut b := CVec.zeros M
  for j in [0:n] do
    -- b_j = conj(w_j), symmetric
    let wr := chirp.re j; let wi := -(chirp.im j)
    b := (b.set! (2 * j) wr).set! (2 * j + 1) wi
    if j != 0 then b := (b.set! (2 * (M - j)) wr).set! (2 * (M - j) + 1) wi
  let fa := fftPow2 a (-1)
  let fb := fftPow2 b (-1)
  let conv := fftPow2 (CVec.mul fa fb) 1
  let inv := 1 / Float.ofNat M
  let mut out := FloatArray.emptyWithCapacity (2 * n)
  for k in [0:n] do
    let cr := conv.re k * inv; let ci := conv.im k * inv
    let wr := chirp.re k; let wi := chirp.im k
    out := (out.push (cr * wr - ci * wi)).push (cr * wi + ci * wr)
  return out

end

/-- FFTW `fft` (forward, unnormalized). -/
def fft (z : CVec) : CVec := dft z (-1)

/-- FFTW `bfft` (backward, unnormalized). -/
def bfft (z : CVec) : CVec := dft z 1

/-- FFTW `ifft = bfft / N`. -/
def ifft (z : CVec) : CVec := CVec.scale (1 / Float.ofNat z.len) (bfft z)

/-- FFTW `rfft` of a real vector: bins `0 … N÷2`. -/
def rfft (x : FloatArray) : CVec :=
  let full := fft (CVec.ofReal x)
  ⟨full.data.extract 0 (2 * (x.size / 2 + 1))⟩

/-- The Hermitian completion of the half-spectrum `X` (bins `0 … N÷2`) of a real signal of length
`N`. -/
def hermitian (X : CVec) (N : Nat) : CVec := Id.run do
  let mut z := CVec.zeros N
  for k in [0:N] do
    if k ≤ N / 2 then
      z := (z.set! (2 * k) (X.re k)).set! (2 * k + 1) (X.im k)
    else
      z := (z.set! (2 * k) (X.re (N - k))).set! (2 * k + 1) (-X.im (N - k))
  return z

/-- FFTW `brfft(X, N)`: the unnormalized real inverse. -/
def brfft (X : CVec) (N : Nat) : FloatArray := CVec.realPart (bfft (hermitian X N))

/-- FFTW `irfft(X, N) = brfft(X, N) / N`. -/
def irfft (X : CVec) (N : Nat) : FloatArray :=
  let s := 1 / Float.ofNat N
  ⟨(brfft X N).data.map (· * s)⟩

/-! ## Real-to-real transforms (FFTW kinds) -/

/-- FFTW's r2r kinds (`FFTW.R2HC = 0 … RODFT11 = 10`). -/
inductive R2RKind where
  | R2HC | HC2R | DHT | REDFT00 | REDFT01 | REDFT10 | REDFT11 | RODFT00 | RODFT01 | RODFT10 | RODFT11
  deriving Repr, BEq, Inhabited, DecidableEq

namespace R2RKind

/-- FFTW's integer code. -/
def code : R2RKind → Nat
  | R2HC => 0 | HC2R => 1 | DHT => 2 | REDFT00 => 3 | REDFT01 => 4 | REDFT10 => 5
  | REDFT11 => 6 | RODFT00 => 7 | RODFT01 => 8 | RODFT10 => 9 | RODFT11 => 10

/-- The kind with an FFTW code. -/
def ofCode? : Nat → Option R2RKind
  | 0 => some R2HC | 1 => some HC2R | 2 => some DHT | 3 => some REDFT00 | 4 => some REDFT01
  | 5 => some REDFT10 | 6 => some REDFT11 | 7 => some RODFT00 | 8 => some RODFT01
  | 9 => some RODFT10 | 10 => some RODFT11 | _ => none

end R2RKind

/-- The real part of the forward FFT of a real sequence. -/
private def fftRe (x : FloatArray) : CVec := fft (CVec.ofReal x)

/-- FFTW `r2r(x, kind)` (the unnormalized definitions of the FFTW manual §4.8), by FFTs of
symmetric extensions:
* `REDFT00` (DCT-I, `N ≥ 2`): extension to `2(N−1)`; `REDFT10` (DCT-II): `Y_k = 2 Σ x_j cos(π(j+½)k/N)`
  from the length-`4N` even-odd extension; `REDFT01` (DCT-III): `Y_k = x₀ + 2 Σ_{j≥1} x_j cos(πj(k+½)/N)`;
  `REDFT11` (DCT-IV): `Y_k = 2 Σ x_j cos(π(j+½)(k+½)/N)`;
* the `RODFT` kinds likewise with sines (`RODFT00` extension to `2(N+1)`);
* `R2HC`: the half-complex `(r₀, r₁, …, r_{N/2}, i_{(N−1)/2}, …, i₁)`, `HC2R` its inverse
  (unnormalized), `DHT`: `Y_k = Σ x_j (cos + sin)(2πjk/N)`. -/
def r2r (x : FloatArray) (kind : R2RKind) : FloatArray := Id.run do
  let N := x.size
  let g := fun (j : Nat) => x.get! j
  match kind with
  | .R2HC =>
    let F := fftRe x
    return ⟨(Array.range N).map fun k => if k ≤ N / 2 then F.re k else F.im (N - k)⟩
  | .HC2R =>
    -- x holds (r₀, …, r_{N/2}, i_{(N-1)/2}, …, i₁); rebuild the spectrum and invert (unnormalized)
    let mut X := CVec.zeros N
    for k in [0:N] do
      let r := if k ≤ N / 2 then g k else g (N - k)
      let i := if k == 0 || 2 * k == N then 0 else if k < N - k then g (N - k) else -(g k)
      X := (X.set! (2 * k) r).set! (2 * k + 1) i
    return CVec.realPart (bfft X)
  | .DHT =>
    let F := fftRe x
    return ⟨(Array.range N).map fun k => F.re k - F.im k⟩
  | .REDFT00 =>
    -- even extension x₀ … x_{N-1} x_{N-2} … x₁ of length 2(N-1)
    let L := 2 * (N - 1)
    let e : FloatArray := ⟨(Array.range L).map fun j => if j < N then g j else g (L - j)⟩
    let F := fftRe e
    return ⟨(Array.range N).map F.re⟩
  | .RODFT00 =>
    -- odd extension 0 x₀ … x_{N-1} 0 −x_{N-1} … −x₀ of length 2(N+1)
    let L := 2 * (N + 1)
    let e : FloatArray := ⟨(Array.range L).map fun j =>
      if j == 0 || j == N + 1 then 0 else if j ≤ N then g (j - 1) else -(g (L - j - 1))⟩
    let F := fftRe e
    return ⟨(Array.range N).map fun k => -(F.im (k + 1))⟩
  | .REDFT10 =>
    -- length-4N extension with x at odd positions (even symmetry): Y_k = Re F_k
    let L := 4 * N
    let e : FloatArray := ⟨(Array.range L).map fun j =>
      if j % 2 == 0 then 0 else if j < 2 * N then g (j / 2) else g ((L - j) / 2)⟩
    let F := fftRe e
    return ⟨(Array.range N).map F.re⟩
  | .RODFT10 =>
    let L := 4 * N
    let e : FloatArray := ⟨(Array.range L).map fun j =>
      if j % 2 == 0 then 0 else if j < 2 * N then g (j / 2) else -(g ((L - j) / 2))⟩
    let F := fftRe e
    return ⟨(Array.range N).map fun k => -(F.im (k + 1))⟩
  | .REDFT01 =>
    -- DCT-III: Y_k = x₀ + 2 Σ_{j≥1} x_j cos(πj(2k+1)/(2N)) = Re(Σ_{j<4N} u_j e^{-2πi j(2k+1)/(4N)})
    let L := 4 * N
    let e : FloatArray := ⟨(Array.range L).map fun j =>
      if j < N then g j else if j == N || j == 3 * N then 0
      else if j < 2 * N then -(g (2 * N - j)) else if j < 3 * N then -(g (j - 2 * N))
      else g (L - j)⟩
    let F := fftRe e
    return ⟨(Array.range N).map fun k => F.re (2 * k + 1) / 2⟩
  | .RODFT01 =>
    -- DST-III: Y_k = (−1)^k x_{N−1} + 2 Σ_{j<N−1} x_j sin(π(j+1)(2k+1)/(2N))
    return ⟨(Array.range N).map fun k => Id.run do
      let mut s := 0.0
      for j in [0:N] do
        let w := if j + 1 == N then 1.0 else 2.0
        let (_, sn) := cossinpiRat ((j + 1) * (2 * k + 1)) (2 * N)
        s := s + w * g j * sn
      return s⟩
  | .REDFT11 =>
    return ⟨(Array.range N).map fun k => Id.run do
      let mut s := 0.0
      for j in [0:N] do
        let (cs, _) := cossinpiRat ((2 * j + 1) * (2 * k + 1)) (4 * N)
        s := s + 2 * g j * cs
      return s⟩
  | .RODFT11 =>
    return ⟨(Array.range N).map fun k => Id.run do
      let mut s := 0.0
      for j in [0:N] do
        let (_, sn) := cossinpiRat ((2 * j + 1) * (2 * k + 1)) (4 * N)
        s := s + 2 * g j * sn
      return s⟩

/-- FFTW.jl `dct(x)`: the orthonormal DCT-II (`REDFT10` scaled by `√(1/(2N))`, bin `0` by `√(1/(4N))`
more: `Y₀ = Σx/√N`, `Y_k = √(2/N) Σ x_j cos(π(2j+1)k/(2N))`). -/
def dct (x : FloatArray) : FloatArray :=
  let N := x.size
  let Y := r2r x .REDFT10
  let s0 := Float.sqrt (1 / (4 * Float.ofNat N))
  let s := Float.sqrt (1 / (2 * Float.ofNat N))
  ⟨(Array.range N).map fun k => Y.get! k * (if k == 0 then s0 else s)⟩

/-- FFTW.jl `idct(y)`: the inverse of `dct` (orthonormal DCT-III). -/
def idct (y : FloatArray) : FloatArray :=
  let N := y.size
  let s0 := Float.sqrt (1 / (4 * Float.ofNat N))
  let s := Float.sqrt (1 / (2 * Float.ofNat N))
  -- REDFT01 of (y₀·s₀·2, y_k·s) … inverts REDFT10 up to the factor: y = r2r(Y', REDFT01)
  let u : FloatArray := ⟨(Array.range N).map fun k => y.get! k * (if k == 0 then 2 * s0 else s)⟩
  let Z := r2r u .REDFT01
  ⟨Z.data.map (· * 1)⟩

end Cartan.Spectral
