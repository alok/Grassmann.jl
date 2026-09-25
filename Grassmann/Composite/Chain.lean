/-
Composite functions of homogeneous elements: `Chain V G`
(Grassmann.jl `src/composite.jl:136-159`, `:360-409`, `:436-539`,
`src/algebra.jl:440-470`, AbstractTensors `AT:405-431`;
port-notes/grassmann-composite.md §4.2.1, §4.2.5, §4.3-4.7).

* `exp`: the scalar `exp(c)` for `G = 0`; the 3D-PGA closed form for bivectors of
  `⟨1,1,1,0⟩` (`C:142-147`); the closed form `cos θ + t·sin θ/θ` (`cosh`/`sinh`, or
  `1 + t` when `t⟑t = 0`) whenever `t⟑t` is (approximately) a scalar; otherwise
  `1 + expm1(multispin(t))` with Julia's generated series on the `Spinor` (even
  `G`) or the `Multivector` (odd `G`).
* `cosh`/`sinh`: Julia's *generic* series (a `Chain` is not a `Multivector`/`Spinor`),
  whose partial sums live in the even half (`cosh`, with `τ = t⟑t`) or in the half
  of the parity of `G` (`sinh`), so the results are typed `Spinor` and
  `Half V (G odd)`.
* `cos t = cosh(I⟑t)`, `sin t = sinh(I⟑t)/I`, `tan t = sin t/cos t`
  (AbstractTensors), with `I⟑t` a chain of grade `n - G` (quirk B2 replicated:
  in spaces with `I² = +1` the "cosine" of a scalar is a `cosh`).
* `log`, `log1p`, `sqrt`, `cbrt`: Julia's generic `qlog`-based definitions, whose
  divisions can fail (`none` / `NaN`), and the scalar functions for `G = 0`.
* `pow`: Julia's contraction shortcut for spaces of dimension ≤ 3 and repeated or
  binary multiplication otherwise.

Results whose container depends on the parity of `G` are `Multivector`s
(`exp`, `log`, ...); `expEven` gives the `Spinor` of an even chain directly.
Tangent spaces are handled only as far as the products stay scalar-valued (as in
the kernels).
-/
import Grassmann.Composite.Dense

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

namespace Composite

variable [Kernels V]

/-- The spinor values `x·1`. -/
@[inline] def scalarV (V : TensorBundle) (l : Layout) (x : Float) : Values Float (l.size V.n) :=
  Values.ofFn fun i => if i.1 = 0 then x else f0

/-- `cosh` of a grade-`g` chain (its coefficients `x`) as a spinor: `cosh(x₀)` for
`g = 0` (Julia `C:456`), otherwise Grassmann's generic series (`C:458-481`) over
`τ = x⟑x`. -/
@[specialize V] def coshChainV (g : Nat) (x : Values Float ((Layout.chain g).size V.n)) : Half V false Float :=
  if g == 0 then Half.scalarF (Float.cosh (getD x 0))
  else
    let τ : Half V false Float := ⟨Kernels.bin .mul (.chain g) (.chain g) (halfLayout false) x x⟩
    Half.addScalar f1 (coshGenericTail (· + ·) Half.smul' Half.sdiv Half.fnorm τ)

/-- `sinh` of a grade-`g` chain (its coefficients `x`) as the half of parity `g`:
`sinh(x₀)` for `g = 0` (Julia `C:515`), otherwise Grassmann's generic series
(`C:517-539`): `S = t`, `term = t⟑τ/6`, next term `term ⟑ (τ/(k(k-1)))`. -/
@[specialize V] def sinhChainV (g : Nat) (x : Values Float ((Layout.chain g).size V.n)) :
    Values Float ((halfLayout (g % 2 == 1)).size V.n) :=
  if g == 0 then scalarV V _ (Float.sinh (getD x 0))
  else
    let lp := halfLayout (g % 2 == 1)
    let τ : Values Float ((halfLayout false).size V.n) :=
      Kernels.bin .mul (.chain g) (.chain g) (halfLayout false) x x
    let t0 : Values Float (lp.size V.n) := embedChain V g lp f1 x
    let mulτ := fun (y : Values Float (lp.size V.n)) => Kernels.bin .mul lp (halfLayout false) lp y τ
    sinhGenericWith (vzip (· + ·)) (fun y k => vmap (· / k) y) vnorm mulτ
      (fun d y => Kernels.bin .mul lp (halfLayout false) lp y (vmap (· / natF d) τ)) t0

/-- The grade of the pseudoscalar `I = V(I)` (the non-tangent generators). -/
@[inline] def pseudoGrade (V : TensorBundle) : Nat := V.n - V.diffvars

/-- The coefficients of `c·I` as a chain of grade `pseudoGrade V`. -/
@[inline] def pseudoValues (V : TensorBundle) (c : Float) :
    Values Float ((Layout.chain (pseudoGrade V)).size V.n) :=
  (Chain.ofBlade (⟨pseudoMask V⟩ : Submanifold V (pseudoGrade V)) c : Chain V _ Float).v

/-- `I ⟑ x` for a grade-`g` chain `x`: the chain of grade `pseudoGrade V - g` (the
pseudoscalar contracts each blade onto one blade, in every metric). -/
@[inline] def mulPseudoChain (g : Nat) (x : Values Float ((Layout.chain g).size V.n)) :
    Values Float ((Layout.chain (pseudoGrade V - g)).size V.n) :=
  Kernels.binProj .mul (.chain (pseudoGrade V)) (.chain g) (.chain (pseudoGrade V - g))
    (pseudoValues V f1) x

/-- `y ⟑ inv(I)` for `y` in layout `la`, projected onto layout `lc` (Julia's right
division `y / I`, AbstractTensors `AT:320`). -/
@[inline] def divPseudo (la lc : Layout) (y : Values Float (la.size V.n)) : Values Float (lc.size V.n) :=
  Kernels.binProj .mul la (.chain (pseudoGrade V)) lc y (pseudoValues V (invPseudoCoef V))

end Composite

namespace Chain

variable {G : Nat} [Kernels V]

/-- The chain's coefficients in layout `l` (`.even`/`.full` for an even `G`, `.odd`/`.full` for
an odd one): the space's embedding kernel (the parity projection of the chain). -/
@[inline] def embedLayout (l : Layout) (c : Chain V G Float) : Values Float (l.size V.n) :=
  if storesGrade G l then embedChain V G l f1 c.v else zeros V l

/-- The chain as the even half (meaningful for even `G`). -/
@[inline] def evenHalf (c : Chain V G Float) : Half V false Float := ⟨c.embedLayout (halfLayout false)⟩

/-- `a + x·c` in layout `l` (`G > 0`: the scalar slot is free). -/
@[inline] def affine (l : Layout) (a x : Float) (c : Chain V G Float) : Values Float (l.size V.n) :=
  if storesGrade G l then vset (embedChain V G l x c.v) 0 a else vset (zeros V l) 0 a

/-- `a + x·c` as a spinor (for even `G > 0`). -/
@[inline] def spinorAffine (a x : Float) (c : Chain V G Float) : Half V false Float :=
  ⟨affine (halfLayout false) a x c⟩

/-- `a + x·c` as a multivector (`G > 0`). -/
@[inline] def mvAffine (a x : Float) (c : Chain V G Float) : Multivector V Float := ⟨affine .full a x c⟩

/-- The chain as a multivector (the embedding kernel). -/
@[inline] def embedMV (c : Chain V G Float) : Multivector V Float := ⟨c.embedLayout .full⟩

/-- The scalar `t⟑t` of a chain when it is structurally a scalar (no kernel): in a plain
signature space the squares of vectors, pseudovectors, pseudoscalars and of every chain of a
space of dimension ≤ 3 are scalars, `Σ cᵢ²·Bᵢ²`. -/
@[inline] def sqScalarFast? (c : Chain V G Float) : Option Float :=
  let s := plainNeg V
  if s != notPlain && (G ≤ 1 || G + 1 ≥ V.n || V.n ≤ 3) then some (weightedSum (plainSq s) (.chain G) c.v)
  else none

/-- The closed form of Julia `exp(t::Chain)` (`src/composite.jl:148-156`): when `t⟑t` is
(approximately) a scalar `h`, `exp t = a + x·t` with `(a, x) = (1, 1)` for `h = 0`,
`(cos θ, sin θ/θ)` for `h < 0` and `(cosh θ, sinh θ/θ)` for `h > 0`,
`θ = √|contraction(t, t)|`; `none` when the series is needed. -/
@[inline] def expClosed? (c : Chain V G Float) : Option (Float × Float) :=
  let h? : Option Float := match sqScalarFast? c with
    | some h => some h
    | none =>
      let sq : Values Float ((halfLayout false).size V.n) :=
        Kernels.bin .mul (.chain G) (.chain G) (halfLayout false) c.v c.v
      let h := getD sq 0
      if isScalarNorms sq.norm h then some h else none
  match h? with
  | none => none
  | some h =>
    if h == f0 then some (f1, f1)
    else
      let θ := Float.sqrt (Float.abs (abs2Sum (.chain G) c.v))
      if h < f0 then some (Float.cos θ, sinOver θ) else some (Float.cosh θ, sinhOver θ)

/-- Julia's 3D-PGA closed form of `exp` for a bivector of `⟨1,1,1,0⟩`
(`src/composite.jl:142-147`): with `u = √|abs2(t)|` and `v = (t∧t)·(-½/u)` (a multiple of
`I`, `I² = 0`), `exp t = (cos u - v sin u) + ((sin u + v cos u) ⟑ t) ⟑ (1/u - v/u²)`, and
`1 + t` for `u < 10⁻⁵`. -/
@[specialize V] def expPGA (c : Chain V G Float) : Half V false Float :=
  let u := Float.sqrt (Float.abs (getD c.abs2.v 0))
  if u < pgaCut then spinorAffine f1 f1 c
  else
    let tt : Values Float ((Layout.chain (G + G)).size V.n) :=
      Kernels.bin .wedge (.chain G) (.chain G) (.chain (G + G)) c.v c.v
    let w := getD tt 0 * (fmhalf / u)
    let cu := Float.cos u
    let su := Float.sin u
    let i : Submanifold V (pseudoGrade V) := ⟨pseudoMask V⟩
    let spin := fun (a b : Float) => Half.addScalar a (Half.ofBlade i b : Half V false Float)
    let bt : Half V false Float :=
      ⟨Kernels.bin .mul (halfLayout false) (.chain G) (halfLayout false) (spin su (w * cu)).v c.v⟩
    spin cu (-(w * su)) + Half.smul' bt (spin (f1 / u) (-(w / (u * u))))

/-- Julia `exp(t::Chain)` for an even grade, as a spinor (`src/composite.jl:136-159`, `C:407`). -/
@[inline] def expEven (c : Chain V G Float) : Half V false Float :=
  if G == 0 then Half.scalarF (F64.exp (getD c.v 0))
  else if isR301 V && G == 2 then expPGA c
  else match expClosed? c with
    | some (a, x) => spinorAffine a x c
    | none => Half.addScalar f1 (Half.expm1 (evenHalf c))

/-- Julia `exp(t::Chain)` (`src/composite.jl:136-159`, `C:407`): a `Spinor` for even `G`, a
`Multivector` (`scalar + odd`) for odd `G`, returned as a multivector. -/
@[inline] def exp (c : Chain V G Float) : Multivector V Float :=
  if G == 0 then Multivector.scalar (F64.exp (getD c.v 0))
  else if G % 2 == 0 && isR301 V && G == 2 then (expPGA c).toMV
  else match expClosed? c with
    | some (a, x) => mvAffine a x c
    | none =>
      if G % 2 == 0 then (Half.addScalar f1 (Half.expm1 (evenHalf c))).toMV
      else Multivector.addScalar f1 (Multivector.expm1 (c.embedMV))

/-- Julia `expm1(t::Chain) = expm1(multispin(t))` (`src/composite.jl:28-30`): the scalar
`expm1` for `G = 0`, the generated series of the `Spinor`/`Multivector` otherwise. -/
@[specialize V] def expm1 (c : Chain V G Float) : Multivector V Float :=
  if G == 0 then Multivector.scalar (F64.expm1 (getD c.v 0))
  else if G % 2 == 0 then (Half.expm1 (evenHalf c)).toMV
  else Multivector.expm1 (toMultivector c)

/-- Julia `log(t::Chain)`: the scalar `log` for `G = 0` (`C:407`), otherwise the generic
`qlog((t - 1)/(t + 1))` (`C:369`) on the `Spinor`/`Multivector` of `t`; `none` where
Julia throws (`inv` undefined). -/
@[specialize V] def log? (c : Chain V G Float) : Option (Multivector V Float) :=
  if G == 0 then some (Multivector.scalar (F64.log (getD c.v 0)))
  else if G % 2 == 0 then (Half.logSeries? (evenHalf c)).map Half.toMultivector
  else Multivector.log? (toMultivector c)

/-- Julia `log(t::Chain)`; `NaN` coefficients where Julia throws. -/
@[inline] def log (c : Chain V G Float) : Multivector V Float := c.log?.getD Multivector.nan

/-- Julia `log1p(t::Chain) = qlog(t/(t + 2))` (`C:370`), or `none`. -/
@[specialize V] def log1p? (c : Chain V G Float) : Option (Multivector V Float) :=
  if G % 2 == 0 then (Half.log1pSeries? (evenHalf c)).map Half.toMultivector
  else Multivector.log1p? (toMultivector c)

/-- Julia `log1p(t::Chain)`; `NaN` coefficients where Julia throws. -/
@[inline] def log1p (c : Chain V G Float) : Multivector V Float := c.log1p?.getD Multivector.nan

/-- Julia `sqrt`/`cbrt` of a chain (`src/composite.jl:436-451`): the scalar root for
`G = 0` (`qrtScalar`), `0` for the zero chain (`isscalar`), else `exp(log(t)/n)`; `none`
where Julia throws (the logarithm's `inv` undefined). -/
@[specialize V] def root? (qrtScalar : Float → Float) (n : Float) (c : Chain V G Float) : Option (Multivector V Float) :=
  if G == 0 then some (Multivector.scalar (qrtScalar (getD c.v 0)))
  else if isScalarNorms c.v.norm f0 then some (Multivector.scalar (qrtScalar f0))
  else if G % 2 == 0 then
    (Half.logSeries? (evenHalf c)).map fun l => Half.toMultivector (Half.exp (Half.sdiv l n))
  else (Multivector.log? (toMultivector c)).map fun l => Multivector.exp (l / n)

/-- Julia `sqrt(t::Chain)`, or `none` where Julia throws. -/
@[inline] def sqrt? (c : Chain V G Float) : Option (Multivector V Float) := root? Float.sqrt f2 c

/-- Julia `sqrt(t::Chain)`; `NaN` coefficients where Julia throws. -/
@[inline] def sqrt (c : Chain V G Float) : Multivector V Float := c.sqrt?.getD Multivector.nan

/-- Julia `cbrt(t::Chain)`, or `none` where Julia throws. -/
@[inline] def cbrt? (c : Chain V G Float) : Option (Multivector V Float) := root? F64.cbrt f3 c

/-- Julia `cbrt(t::Chain)`; `NaN` coefficients where Julia throws. -/
@[inline] def cbrt (c : Chain V G Float) : Multivector V Float := c.cbrt?.getD Multivector.nan

/-- Julia `cosh(t::Chain)`: `cosh(c₀)` for `G = 0` (`C:456`), otherwise the generic series
(`C:458-481`); a spinor. -/
@[inline] def cosh (c : Chain V G Float) : Half V false Float := coshChainV G c.v

/-- Julia `sinh(t::Chain)`: `sinh(c₀)` for `G = 0` (`C:515`), otherwise the generic series
(`C:517-539`); the half of the parity of `G`. -/
@[inline] def sinh (c : Chain V G Float) : Half V (G % 2 == 1) Float := ⟨sinhChainV G c.v⟩

/-- `tanh t = sinh t / cosh t` (AbstractTensors `AT:419`); `NaN` coefficients where the
inverse of `cosh t` is undefined. -/
@[specialize V] def tanh (c : Chain V G Float) : Half V (G % 2 == 1) Float :=
  let lp := halfLayout (G % 2 == 1)
  ⟨Kernels.bin .mul lp (halfLayout false) lp c.sinh.v (Half.invD c.cosh).v⟩

/-- AbstractTensors `cos(t) = cosh(I ⟑ t)` (`AT:407`) of a chain: a spinor. -/
@[specialize V] def cos (c : Chain V G Float) : Half V false Float :=
  coshChainV (pseudoGrade V - G) (mulPseudoChain G c.v)

/-- AbstractTensors `sin(t) = sinh(I ⟑ t)/I` (`AT:408`) of a chain: the half of the parity
of `G`. -/
@[specialize V] def sin (c : Chain V G Float) : Half V (G % 2 == 1) Float :=
  let g' := pseudoGrade V - G
  ⟨divPseudo (halfLayout (g' % 2 == 1)) (halfLayout (G % 2 == 1)) (sinhChainV g' (mulPseudoChain G c.v))⟩

/-- AbstractTensors `tan(t) = sin(t)/cos(t)` (`AT:409`) of a chain; `NaN` coefficients where
the inverse of `cos t` is undefined. -/
@[specialize V] def tan (c : Chain V G Float) : Half V (G % 2 == 1) Float :=
  let lp := halfLayout (G % 2 == 1)
  ⟨Kernels.bin .mul lp (halfLayout false) lp c.sin.v (Half.invD c.cos).v⟩

/-- Julia's scalar recursion of `^(sq::Chain{V,0}, d)` inside the `mdims ≤ 3` chain power
(`src/algebra.jl:443-446`): `x` for `d = 1`, else `(x·x)^⌊d/2⌋` (Julia's `Float64^Int`)
times `x` when `d` is odd. -/
def scalarPow3 (x : Float) (d : Nat) : Float :=
  if d == 1 then x
  else
    let x2 := x * x
    let d2 := d / 2
    let v := if d2 == 1 then x2 else F64.powInt x2 d2
    if d % 2 == 0 then v else v * x

/-- Julia `t ^ k` for a chain (`src/algebra.jl:440-470`): `t` for `k = 1`; in spaces of
dimension ≤ 3 (no tangent variables) `sq^⌊k/2⌋` times `t` when `k` is odd, with
`sq = contraction(~t, t)`; otherwise Julia's repeated/binary multiplication; and
`inv(t)^|k|` for `k < 0` (Julia returns `t` or `One` there). -/
@[specialize V] def pow (c : Chain V G Float) (k : Int) : Multivector V Float :=
  if k == 1 then toMultivector c
  else
    let c' := if k < 0 then c.inv else c
    let n := k.natAbs
    if n == 0 then Multivector.one
    else if n == 1 then toMultivector c'
    else if V.n ≤ 3 && V.diffvars == 0 then
      let sq := getD ((contraction (~c') c' : Chain V (G - G) Float).cast (Nat.sub_self G)).v 0
      let v := scalarPow3 sq (n / 2)
      if n % 2 == 0 then Multivector.scalar v else toMultivector (v * c')
    else if G % 2 == 0 then Half.toMultivector (powJulia Half.smul' Spinor.one (evenHalf c') n)
    else powJulia (· * ·) Multivector.one (toMultivector c') n

/-- Julia `b ^ t = exp(t ⟑ log(b))` for a real base (AbstractTensors `AT:326`). -/
@[inline] def rpow (b : Float) (c : Chain V G Float) : Multivector V Float := exp (c * F64.log b)

end Chain

end Grassmann
