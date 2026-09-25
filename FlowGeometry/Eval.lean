import FlowGeometry.Types
import FlowGeometry.Solve

/-!
# Evaluating the analytic profiles

Every profile family of FlowGeometry.jl `src/profiles.jl` as a function of the chord fraction
`x`: the value `p(x)` and the slope `profileslope(p, x)`. Julia folds the coefficient fits
(`naca4`, `naca5`, the `Thickness` 5×5 solve) at compile time with `@pure`/`@generated`, and
recomputes the two 4×4 solves of `Modified` on every call; here `Profile.eval` computes all of them
once, into an `Eval` whose constructors hold the coefficients as unboxed `Float` fields, and
`Eval.value`/`Eval.slope` are straight-line code.

The operation order is Julia's, so values agree bit for bit (`x^2` and `x^3` with literal exponents
are `x*x` and `x*x*x`, `x^4` is Julia's compensated power by squaring, `F64.literalPow`; the
elementary functions are Julia's own kernels from `JuliaBase`). Julia's quirks are kept
(port notes §4.2, §8.4): the `ParabolicArc` slope uses `t/400`, the `Modified` leading-edge row is
`(1,1,1,1)`, the `NACA5` slope has no `/6` and the reflexed fits are Julia's, `NACA6` swaps `g` and
`h` on the value path and takes `log(a-x)` of a negative number (`NaN`, Julia's `DomainError`) on
the slope path. Julia's `NACA6A` throws below `x = 0.87437` (a `Float64 + Values` `MethodError`);
the port evaluates the evident scalar intent `naca6(x, 0.8, 0, 0)` there (defect FG-B3, no golden).
-/

namespace FlowGeometry

open JuliaBase

/-! ## Coefficient fits (Julia `@pure` helpers) -/

/-- Julia `x^4` (`Base.literal_pow` → `pow_body(x, 4)`, `pow.jl:120-146`): the compensated power
by squaring, unrolled for `n = 4` as Julia's constant propagation does (bit-identical to
`F64.literalPow x 4`). -/
@[inline] def pow4 (x : Float) : Float :=
  let h1 := x * x
  let l1 := Float.fma x x (-h1) + x * f64! 2.0 * f64! -0.0
  let h2 := h1 * h1
  let l2 := Float.fma h1 h1 (-h2) + h1 * f64! 2.0 * l1
  let err := Float.fma f64! 1.0 l2 (h2 * f64! 0.0)
  if F64.isfinite h2 && F64.isfinite err then h2 * f64! 1.0 + err else h2 * f64! 1.0

/-- Julia `approx(x, y::Values{N}) = poly(x, Val(N))⋅y` (`profiles.jl:15-18`): `Σ yᵢ xⁱ` with the
powers `1, x, x*x, x*x*x, x^4` summed left to right. -/
def approx (x : Float) (ys : Array Float) : Float :=
  let pw (i : Nat) : Float :=
    match i with
    | 0 => f64! 1.0
    | 1 => x
    | 2 => x * x
    | 3 => x * x * x
    | k => F64.literalPow x k
  if ys.size == 0 then 0
  else (List.range (ys.size - 1)).foldl (fun acc i => acc + pw (i + 1) * ys[i + 1]!) (pw 0 * ys[0]!)

/-- Julia `clarky(te = 0.0021)` (`profiles.jl:122`): the NACA 4-digit thickness coefficients
`(0.2969, -0.1260, -0.3516 + 1e-16, 0.2843, te - 0.1036)`. -/
def clarky (te : Float) : Array Float :=
  #[f64! 0.2969, f64! -0.1260, f64! -0.3516 + f64! 1e-16, f64! 0.2843, te - f64! 0.1036]

/-- Julia `tailslope(x) = -approx(x, (31/200, 151/300, -109/40, 43/6, -5/2))` (`profiles.jl:139`):
the trailing-edge slope as a function of the maximum-thickness position. -/
def tailslope (x : Float) : Float :=
  -approx x #[(31 : Float) / 200, (151 : Float) / 300, (-109 : Float) / 40, (43 : Float) / 6,
    (-5 : Float) / 2]

/-- Julia `riegel(x) = -(2.24 - 5.42x + 12.3x²)/(10(1 - 0.878x))` (`profiles.jl:140`, unused
upstream). -/
def riegel (x : Float) : Float :=
  -((f64! 2.24 - f64! 5.42 * x) + f64! 12.3 * (x * x)) / (10 * (1 - f64! 0.878 * x))

/-- Julia `radius(t) = t^2*((a0/0.2)^2/2)` with `a0 = 0.2969` (`profiles.jl:123`): the leading-edge
radius of a thickness `t`. -/
def radius (t : Float) : Float :=
  let q := f64! 0.2969 / f64! 0.2
  t * t * ((q * q) / 2)

/-- Julia `Y(x) = (√x, x, x², x³, x⁴)` (`profiles.jl:112`). -/
def basisY (x : Float) : Array Float := #[x.sqrt, x, x * x, x * x * x, pow4 x]

/-- Julia `dY(x) = (0.5/√x, 1, 2x, 3x², 4x³)` (`profiles.jl:113`). -/
def basisDY (x : Float) : Array Float := #[f64! 0.5 / x.sqrt, 1, 2 * x, 3 * (x * x), 4 * (x * x * x)]

/-- Julia `clarky(te, x, ts = tailslope(x), n = 0.1, y = 0.078)` (`profiles.jl:142-144`): the
`Thickness` coefficients from the 5×5 system with rows `Y(x), dY(x), Y(1), dY(1), Y(n)` and
right-hand side `(0.1, 0, te, ts, y)`. -/
def clarky5 (te x : Float) : Array Float :=
  solve5 #[basisY x, basisDY x, basisY 1, basisDY 1, basisY (f64! 0.1)]
    #[f64! 0.1, 0, te, tailslope x, f64! 0.078]

/-- Julia `modified(::Modified{t,m,te})` (`profiles.jl:173-175`): `(t/100, i, (m%10)/10, te/100)`
with `i = Int(m÷10)`, replaced by `6√3` when it is `9`. -/
def modifiedParams (t m te : Num) : Float × Num × Float × Float :=
  let i := m.div10
  let i : Num := match i with
    | .int n => .int n
    | .float x => .int (F64.toIntTrunc x)
  let i : Num := if i.toFloat == 9 then .float (6 * Float.sqrt 3) else i
  (t.toFloat / 100, i, m.rem10.toFloat / 10, te.toFloat / 100)

/-- Julia `D(x)` (`profiles.jl:159`): `(1, x₁, x₁², x₁³)` with `x₁ = 1 - x`. -/
def basisD (x : Float) : Array Float := let x1 := 1 - x; #[1, x1, x1 * x1, x1 * x1 * x1]
/-- Julia `dD(x)` (`profiles.jl:160`): `(0, -1, 2x₁, -3x₁²)` with `x₁ = x - 1`. -/
def basisDD (x : Float) : Array Float := let x1 := x - 1; #[0, -1, 2 * x1, -3 * (x1 * x1)]
/-- Julia `ddD(x)` (`profiles.jl:161`): `(0, 0, 2, -6(x-1))`. -/
def basisDDD (x : Float) : Array Float := #[0, 0, 2, -6 * (x - 1)]
/-- Julia `A(x)` (`profiles.jl:163`): `(√x, x, x², x³)`. -/
def basisA (x : Float) : Array Float := #[x.sqrt, x, x * x, x * x * x]
/-- Julia `dA(x)` (`profiles.jl:164`): `(0.5/√x, 1, 2x, 3x²)`. -/
def basisDA (x : Float) : Array Float := #[f64! 0.5 / x.sqrt, 1, 2 * x, 3 * (x * x)]
/-- Julia `ddA(x)` (`profiles.jl:165`): `(-1/(4x√x), 0, 2, 6x)`. -/
def basisDDA (x : Float) : Array Float := #[-1 / (4 * x * x.sqrt), 0, 2, 6 * x]

/-- Julia `a ⋅ b` of two vectors (Grassmann contraction of `Chain{ℝn,1}`s): `Σ aᵢbᵢ`, left to
right. -/
def dot (a b : Array Float) : Float :=
  if a.size == 0 then 0
  else (List.range (a.size - 1)).foldl (fun acc i => acc + a[i + 1]! * b[i + 1]!) (a[0]! * b[0]!)

/-- Julia `modified(t, i, x, te = 0.002, ts = tailslope(x))` (`profiles.jl:167-171`): the front
coefficients `a` (basis `A`, rows `A(x), dA(x), ddA(x), (1,1,1,1)`) and rear coefficients `d`
(basis `D`, rows `D(x), dD(x), D(1), dD(1)`). The fourth front row `(1,1,1,1)` is Julia's (the
intent is `(1,0,0,0)`, pinning `a₀`); NACA 0012-64 therefore has a negative thickness near the
leading edge, as in Julia. -/
def modifiedCoeffs (t : Float) (i : Num) (x te : Float) : Array Float × Array Float :=
  let d := solve4 #[basisD x, basisDD x, basisD 1, basisDD 1] #[f64! 0.1, 0, te, tailslope x]
  let rhs4 := (1 / (5 * t)) * (2 * radius ((f64! 0.2 * i.toFloat) / 6)).sqrt
  let a := solve4 #[basisA x, basisDA x, basisDDA x, #[1, 1, 1, 1]]
    #[f64! 0.1, 0, dot (basisDDD x) d, rhs4]
  (a, d)

/-- Julia `naca4(n)` (`profiles.jl:203-207`): the digits of `string(n, pad = 2)` give
`(M/100, P/10)` (only the first two digits are read). -/
def naca4Decode (n : Nat) : Float × Float :=
  let ds := (Nat.toDigits 10 n)
  let ds := if ds.length < 2 then '0' :: ds else ds
  let dig (c : Char) : Float := (c.toNat - '0'.toNat).toUInt64.toFloat
  (dig ds[0]! / 100, dig ds[1]! / 10)

/-- Julia `C(x) = (1, x, x²)` (`profiles.jl:194`). -/
def basisC (x : Float) : Array Float := #[1, x, x * x]
/-- Julia `dC(x) = (0, 1, 2x)` (`profiles.jl:195`). -/
def basisDC (x : Float) : Array Float := #[0, 1, 2 * x]

/-- Julia `naca4(m, p)` (`profiles.jl:197-201`): the front and rear quadratic camber coefficients
(rows `C(p), dC(p), C(0)` and `C(p), dC(p), C(1)`, right-hand side `(m, 0, 0)`). `p = 0` makes
the front system singular: `NaN` coefficients, never used. -/
def naca4Coeffs (m p : Float) : Array Float × Array Float :=
  (solve3 #[basisC p, basisDC p, basisC 0] #[m, 0, 0], solve3 #[basisC p, basisDC p, basisC 1] #[m, 0, 0])

/-- Julia `naca5(n)` (`profiles.jl:228-248`): from the digits `C, P, R` of `string(n)`, the
camber scale `m·k₁`, the transition point `r` and `k₂/k₁` (`0` for the standard, `R = 0`, lines),
from Julia's polynomial fits in `p = P/20`. `none` where Julia throws (fewer than three digits,
`R ∉ {0, 1}`). -/
def naca5Decode (n : Nat) : Option (Float × Float × Float) :=
  let ds := Nat.toDigits 10 n
  if ds.length < 3 then none else
  let dig (c : Char) : Nat := c.toNat - '0'.toNat
  let C := dig ds[0]!
  let P := dig ds[1]!
  let R := dig ds[2]!
  let m := C.toUInt64.toFloat / 2
  let p := P.toUInt64.toFloat / 20
  let q (a b : Int) : Float := Float.ofInt a / Float.ofInt b
  if R == 0 then
    let r := approx p #[q (-1) 250, q 359 300, q 7 10, q 10 3, 0]
    let k1 := approx p #[q 284037 200, q (-3296847) 100, q 4296829 15, -1087744, q 4544800 3]
    some (m * k1, r, 0)
  else if R == 1 then
    let r := approx p #[q 17 500, q 26 15, -2, q 32 3]
    let k1 := approx p #[q 72269 250, q (-583261) 150, q 89864 5, q 83920 3]
    let k1k2 := approx p #[q 10763 50000, q 12081 25000, q (-87457) 2500, q 10691 125]
    some (m * k1, r, k1k2)
  else none

/-- Julia `naca6(n::NACA6)` (`profiles.jl:299-305`): per mean line, `Cl/(2π(1+a))`, `a`, and the
constants `h`, `g` (`NaN` for `a = 1`, unused there). -/
def naca6Decode (a cl : FloatArray) : FloatArray × FloatArray × FloatArray :=
  let twoPi := f64! 6.283185307179586
  let n := a.size
  let cla := floatsOfFn n fun i => cl.get! i / (twoPi * (1 + a.get! i))
  let gs := floatsOfFn n fun i =>
    let ai := a.get! i
    let a1 := 1 - ai
    (-((ai * ai) * (F64.log ai / f64! 2.0 - f64! 0.25) + f64! 0.25)) / a1
  let hs := floatsOfFn n fun i =>
    let a1 := 1 - a.get! i
    let a12 := (a1 * a1) / 2
    (a12 * F64.log a1 - a12 / 2) / a1 + gs.get! i
  (cla, hs, gs)

/-- Julia `naca6(x, a, g, h)` (`profiles.jl:280-289`): one 6-series mean line (value). -/
@[inline] def naca6Value (x a g h : Float) : Float :=
  let x1 := 1 - x
  if a == 1 then -(x1 * F64.log x1 + x * F64.log x)
  else
    let a1 := 1 - a
    let ax := a - x
    let x12 := x1 * x1
    let ax2 := ax * ax
    ((ax2 * F64.log ax.abs - x12 * F64.log x1) + (x12 - ax2) / 2) / (2 * a1) - x * F64.log x + g - h * x

/-- Julia `naca6(x, a, h)` (`profiles.jl:290-297`): one 6-series mean line (slope); `log(a - x)`
of a negative number is `NaN` (Julia's `DomainError`). -/
@[inline] def naca6Slope (x a h : Float) : Float :=
  if a == 1 then F64.log (1 - x) - F64.log x
  else
    let x1 := 1 - x
    let ax := a - x
    (x1 * F64.log x1 - ax * F64.log ax) / (1 - a) - F64.log x - 1 - h

/-! ## Compiled profiles -/

/-- A profile's evaluation data: its family and precomputed coefficients, unboxed. -/
inductive Eval where
  /-- `FlatPlate`: `0`. -/
  | zero
  /-- `ParabolicArc`: `k = t/25`, and `t`. -/
  | parabolic (k t : Float)
  /-- `CircularArc`: `t = T/100` and the radius `r`. -/
  | circular (t r : Float)
  /-- `ClarkY`/`Thickness`: `5t` and the coefficients of `Y(x) = (√x, x, x², x³, x⁴)`. -/
  | poly5 (t5 a0 a1 a2 a3 a4 : Float)
  /-- `Modified`: `5t`, the switch point `p`, the front (`A`) and rear (`D`) coefficients. -/
  | modified (t5 p a0 a1 a2 a3 d0 d1 d2 d3 : Float)
  /-- `NACA4`: the switch point `p`, the front and rear coefficients of `C(x) = (1, x, x²)`. -/
  | naca4 (p f0 f1 f2 r0 r1 r2 : Float)
  /-- `NACA5`: `m·k₁`, the transition `r`, `k₂/k₁`. -/
  | naca5 (mk1 r k : Float)
  /-- `NACA6`: per mean line `Cl/(2π(1+a))`, `a`, and the decoded `h`, `g`. -/
  | naca6 (cla a h g : FloatArray)
  /-- `NACA6A`: `c/36π` and `c`. -/
  | naca6A (k c : Float)
  /-- Not callable (Julia: no method; `UpperArc`/`LowerArc`, or a `NACA5` digit string Julia
  cannot decode): `NaN`. -/
  | none
  deriving Inhabited

/-- `true` outside Julia's evaluation range `0 ≤ x ≤ 1` (`x<0 || x>1`, so `NaN` is inside). -/
@[inline] def outside (x : Float) : Bool := x < f64! 0.0 || x > f64! 1.0

/-- Julia `thickness(x, a, t)` (`profiles.jl:115-117`). -/
@[inline] def poly5Value (t5 a0 a1 a2 a3 a4 x : Float) : Float :=
  if outside x then 0
  else t5 * ((((x.sqrt * a0 + x * a1) + (x * x) * a2) + (x * x * x) * a3) + pow4 x * a4)

/-- Julia `thickness_slope(x, a, t)` (`profiles.jl:118-120`). -/
@[inline] def poly5Slope (t5 a0 a1 a2 a3 a4 x : Float) : Float :=
  if outside x then 0
  else t5 * ((((f64! 0.5 / x.sqrt) * a0 + f64! 1.0 * a1) + (2 * x) * a2) + (3 * (x * x)) * a3 +
    (4 * (x * x * x)) * a4)

/-- The `NACA5` value (`profiles.jl:251-259`). -/
@[inline] def naca5Value (mk1 p k x : Float) : Float :=
  if outside x then 0 else
  let p3 := p * p * p
  let q := 1 - p
  let inner :=
    if x < p then
      let d := x - p
      d * d * d - (if k != 0 then k * x * (q * q * q) else 0)
    else if k != 0 then
      let d := x - p
      k * (d * d * d - x * (q * q * q))
    else 0
  mk1 * (p3 * (1 - x) + inner) / 6

/-- The `NACA5` slope (`profiles.jl:260-268`; Julia's, without the `/6`). -/
@[inline] def naca5Slope (mk1 p k x : Float) : Float :=
  if outside x then 0 else
  let q := 1 - p
  let inner :=
    if x < p then
      let d := p - x
      3 * (d * d) - (if k != 0 then k * (q * q * q) else 0)
    else if k != 0 then
      let d := p - x
      (3 * k) * (d * d - q * q * q)
    else 0
  mk1 * (-(p * p * p) + inner)

/-- The `ParabolicArc` value (`profiles.jl:76`). -/
@[inline] def parabolicValue (k x : Float) : Float := if outside x then 0 else k * x * (1 - x)

/-- The `ParabolicArc` slope (`profiles.jl:77`, Julia's `t/400`). -/
@[inline] def parabolicSlope (t x : Float) : Float := if outside x then 0 else (1 - 2 * x) * t / 400

/-- The `CircularArc` value (`profiles.jl:87-93`). -/
@[inline] def circularValue (t r x : Float) : Float :=
  if outside x then 0 else r * (F64.sin (F64.acos ((x - f64! 0.5) / r)) - 1) + t

/-- The `CircularArc` slope (`profiles.jl:94-100`). -/
@[inline] def circularSlope (t x : Float) : Float :=
  if outside x then 0
  else
    let t4 := 4 * t
    let xc := t4 * (2 * x - 1)
    let q := 1 + t * t4
    Float.neg xc / (q * q - xc * xc).sqrt

/-- The `Modified` value (`profiles.jl:178-181`). -/
@[inline] def modifiedValue (t5 p a0 a1 a2 a3 d0 d1 d2 d3 x : Float) : Float :=
  if outside x then 0
  else if x < p then t5 * (((x.sqrt * a0 + x * a1) + (x * x) * a2) + (x * x * x) * a3)
  else
    let x1 := 1 - x
    t5 * (((f64! 1.0 * d0 + x1 * d1) + (x1 * x1) * d2) + (x1 * x1 * x1) * d3)

/-- The `Modified` slope (`profiles.jl:182-185`). -/
@[inline] def modifiedSlope (t5 p a0 a1 a2 a3 d0 d1 d2 d3 x : Float) : Float :=
  if outside x then 0
  else if x < p then
    t5 * ((((f64! 0.5 / x.sqrt) * a0 + f64! 1.0 * a1) + (2 * x) * a2) + (3 * (x * x)) * a3)
  else
    let x1 := x - 1
    t5 * (((f64! 0.0 * d0 + f64! -1.0 * d1) + (2 * x1) * d2) + (-3 * (x1 * x1)) * d3)

/-- The `NACA4` value (`profiles.jl:210-214`). -/
@[inline] def naca4Value (p f0 f1 f2 r0 r1 r2 x : Float) : Float :=
  if outside x then 0
  else if x < p then (f64! 1.0 * f0 + x * f1) + (x * x) * f2
  else (f64! 1.0 * r0 + x * r1) + (x * x) * r2

/-- The `NACA4` slope (`profiles.jl:215-219`). -/
@[inline] def naca4Slope (p f0 f1 f2 r0 r1 r2 x : Float) : Float :=
  if outside x then 0
  else if x < p then (f64! 0.0 * f0 + f64! 1.0 * f1) + (2 * x) * f2
  else (f64! 0.0 * r0 + f64! 1.0 * r1) + (2 * x) * r2

/-- `0.87437`, the end of the `NACA6A` curved part. -/
def naca6AEnd : Float := f64! 0.87437

namespace Eval

/-- Julia `p(x)`: the profile's value at the chord fraction `x`. -/
def value (e : Eval) (x : Float) : Float :=
  match e with
  | zero => 0
  | parabolic k _ => parabolicValue k x
  | circular t r => circularValue t r x
  | poly5 t5 a0 a1 a2 a3 a4 => poly5Value t5 a0 a1 a2 a3 a4 x
  | modified t5 p a0 a1 a2 a3 d0 d1 d2 d3 => modifiedValue t5 p a0 a1 a2 a3 d0 d1 d2 d3 x
  | naca4 p f0 f1 f2 r0 r1 r2 => naca4Value p f0 f1 f2 r0 r1 r2 x
  | naca5 mk1 r k => naca5Value mk1 r k x
  | naca6 cla a h g =>
    if x < f64! 1e-7 || x > f64! 1.0 - f64! 1e-7 then 0
    else
      -- the value path destructures `(Cla, a, g, h) = naca6(n)`, i.e. swaps `g` and `h`
      let term (i : Nat) := cla.get! i * naca6Value x (a.get! i) (h.get! i) (g.get! i)
      (List.range (cla.size - 1)).foldl (fun acc i => acc + term (i + 1)) (term 0)
  | naca6A k _ =>
    if outside x then 0
    else if x < naca6AEnd then k * naca6Value x (f64! 0.8) 0 0
    else k * (f64! 0.34173943292855025 - f64! 2.773248454778759 * (x - naca6AEnd))
  | none => F64.nan

/-- Julia `profileslope(p, x)`. -/
def slope (e : Eval) (x : Float) : Float :=
  match e with
  | zero => 0
  | parabolic _ t => parabolicSlope t x
  | circular t _ => circularSlope t x
  | poly5 t5 a0 a1 a2 a3 a4 => poly5Slope t5 a0 a1 a2 a3 a4 x
  | modified t5 p a0 a1 a2 a3 d0 d1 d2 d3 => modifiedSlope t5 p a0 a1 a2 a3 d0 d1 d2 d3 x
  | naca4 p f0 f1 f2 r0 r1 r2 => naca4Slope p f0 f1 f2 r0 r1 r2 x
  | naca5 mk1 r k => naca5Slope mk1 r k x
  | naca6 cla a h _ =>
    if x < f64! 1e-7 || x > f64! 1.0 - f64! 1e-7 then 0
    else
      let term (i : Nat) := cla.get! i * naca6Slope x (a.get! i) (h.get! i)
      (List.range (cla.size - 1)).foldl (fun acc i => acc + term (i + 1)) (term 0)
  | naca6A k c =>
    if outside x then 0
    else if x < naca6AEnd then k * naca6Slope x (f64! 0.8) 0
    else f64! -0.0245209 * c
  | none => F64.nan

end Eval

/-- Julia `36π` = `Float64(36) * Float64(π)`. -/
def thirtySixPi : Float := 36 * f64! 3.141592653589793

/-- The loop of `mapFloats` (top level and `@[specialize]`, so that `f` is inlined into it). -/
@[specialize] def mapFloatsLoop (f : Float → Float) : Nat → Nat → FloatArray → FloatArray
  | 0, _, acc => acc
  | k + 1, i, acc => mapFloatsLoop f k (i + 1) (acc.set! i (f (acc.get! i)))

/-- `f` applied to every entry (a tail-recursive loop, specialized at each call site). The result
is written in place into a copy of `xs` (one `memcpy`, then no allocation per entry: a
`FloatArray.push` is an out-of-line runtime call, docs/PERF.md). -/
@[inline] def mapFloats (xs : FloatArray) (f : Float → Float) : FloatArray :=
  mapFloatsLoop f xs.size 0 xs

namespace Eval

/-- The values at every point of `xs` (Julia `p.(xs)`): one match on the family, then a loop
specialized to it. -/
def valuesOn (e : Eval) (xs : FloatArray) : FloatArray :=
  match e with
  | poly5 t5 a0 a1 a2 a3 a4 => mapFloats xs (poly5Value t5 a0 a1 a2 a3 a4)
  | naca5 mk1 r k => mapFloats xs (naca5Value mk1 r k)
  | naca4 p f0 f1 f2 r0 r1 r2 => mapFloats xs (naca4Value p f0 f1 f2 r0 r1 r2)
  | modified t5 p a0 a1 a2 a3 d0 d1 d2 d3 => mapFloats xs (modifiedValue t5 p a0 a1 a2 a3 d0 d1 d2 d3)
  | circular t r => mapFloats xs (circularValue t r)
  | parabolic k _ => mapFloats xs (parabolicValue k)
  | e => mapFloats xs e.value

/-- The slopes at every point of `xs` (Julia `profileslope.(Ref(p), xs)`). -/
def slopesOn (e : Eval) (xs : FloatArray) : FloatArray :=
  match e with
  | poly5 t5 a0 a1 a2 a3 a4 => mapFloats xs (poly5Slope t5 a0 a1 a2 a3 a4)
  | naca5 mk1 r k => mapFloats xs (naca5Slope mk1 r k)
  | naca4 p f0 f1 f2 r0 r1 r2 => mapFloats xs (naca4Slope p f0 f1 f2 r0 r1 r2)
  | modified t5 p a0 a1 a2 a3 d0 d1 d2 d3 => mapFloats xs (modifiedSlope t5 p a0 a1 a2 a3 d0 d1 d2 d3)
  | circular t _ => mapFloats xs (circularSlope t)
  | e => mapFloats xs e.slope

end Eval

/-- Precompute a profile's coefficients (Julia's `@pure`/`@generated` folding). `UpperArc` and
`LowerArc` are not callable in Julia: `Eval.none`. -/
def Profile.eval : Profile → Eval
  | .flatPlate _ => .zero
  | .parabolicArc t _ => .parabolic (t.toFloat / 25) t.toFloat
  | .circularArc T _ =>
    let t := T.toFloat / 100
    .circular t ((t + 1 / (4 * t)) / 2)
  | .clarkY t te _ =>
    let a := clarky (te.toFloat / 100)
    .poly5 (5 * (t.toFloat / 100)) a[0]! a[1]! a[2]! a[3]! a[4]!
  | .thickness t x te _ =>
    let a := clarky5 (te.toFloat / 100) (x.toFloat / 10)
    .poly5 (5 * (t.toFloat / 100)) a[0]! a[1]! a[2]! a[3]! a[4]!
  | .modified t m te _ =>
    let (t, i, p, te) := modifiedParams t m te
    let (a, d) := modifiedCoeffs t i p te
    .modified (5 * t) p a[0]! a[1]! a[2]! a[3]! d[0]! d[1]! d[2]! d[3]!
  | .naca4 n _ =>
    let (m, p) := naca4Decode n
    let (f, r) := naca4Coeffs m p
    .naca4 p f[0]! f[1]! f[2]! r[0]! r[1]! r[2]!
  | .naca5 n _ =>
    (match naca5Decode n with
      | some (mk1, r, k) => .naca5 mk1 r k
      | Option.none => .none)
  | .naca6 a cl _ =>
    let (cla, h, g) := naca6Decode a cl
    .naca6 cla a h g
  | .naca6A c _ => .naca6A (c.toFloat / thirtySixPi) c.toFloat
  | .upperArc _ | .lowerArc _ => .none

namespace Profile

/-- Julia `p(x)` = `profile(p, x)` (`profiles.jl:37`). (For repeated evaluation, compute
`p.eval` once and use `Eval.value`.) -/
def value (p : Profile) (x : Float) : Float := p.eval.value x

/-- Julia `profileslope(p, x)` (and `p'(x)`, `profiles.jl:51-53`). -/
def slope (p : Profile) (x : Float) : Float := p.eval.slope x

/-- Julia `profile(p, x, c, x0) = c·profile(p, (x-x0)/c)` (`profiles.jl:38`; `FlatPlate` gives
`0.0`, `profiles.jl:63`). -/
def valueAt (p : Profile) (x c : Float) (x0 : Float := 0) : Float :=
  match p with
  | .flatPlate _ => 0
  | _ => p.value ((x - x0) / c) * c

/-- Julia `profileslope(p, x, c, x0) = profileslope(p, (x-x0)/c)` (`profiles.jl:39`). -/
def slopeAt (p : Profile) (x c : Float) (x0 : Float := 0) : Float :=
  match p with
  | .flatPlate _ => 0
  | _ => p.slope ((x - x0) / c)

/-- Julia `profileangle(p, x, c, x0) = atan(profileslope(p, x, c, x0))` (`profiles.jl:40`). -/
def angleAt (p : Profile) (x c : Float) (x0 : Float := 0) : Float := F64.atan (p.slopeAt x c x0)

end Profile

end FlowGeometry
