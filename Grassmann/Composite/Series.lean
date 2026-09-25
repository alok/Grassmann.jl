/-
The power-series loops of Grassmann's composite functions (`src/composite.jl`;
port-notes/grassmann-composite.md §4.1).

Every series in `composite.jl` (`expm1`, `cosh`, `sinh`, `qlog`) runs the same
stopping rule over a 3-slot state `norms = (previous term norm, current term
norm, previous partial-sum norm)`:

```
while (norms[2] < norms[1] || norms[2] > 1) [&& k ≤ cap]
    S += term
    ns = norm(S)
    ns ≈ norms[3] && break           # the partial-sum *norm* stopped changing (rtol √eps)
    term = next(term, k)
    norms = (norms[2], norm(term), ns)
    k += step
```

It is the observable definition of the values Julia prints (accuracy ~1e-8…1e-12,
not 1 ulp), so it is reproduced exactly: `seriesLoop` below, generic over the
carrier (a `Values` vector, a pair of floats) with the carrier operations as
explicit arguments, `@[specialize]`d so every instance compiles to a
tail-recursive loop over unboxed data (DESIGN.md §2 rules 2-3).

Julia has two flavours, and both are needed:

* the **generic** loops (`C:31-51`, `C:458-481`, `C:517-539`), used for
  `Single`, `Couple`, `Chain` and every other non-`Multivector`/`Spinor`
  argument: `norms[3]` starts at the first norm, there is no iteration cap,
  and the next term is `term ⟑ (t/k)`;
* the **generated** loops for `Multivector`/`Spinor` (`C:54-81`, `C:483-513`,
  `C:541-570`): a `scalar(b) ≈ norm(b)` shortcut, `norms[3]` starts at `0`, the
  cap `k ≤ 10000`, and the next term is `(term/k) ⟑ b` (each left coefficient
  divided before multiplying).

Deviations (port-notes §8.3): the generic loops also stop after 10000 terms
(Julia never terminates on some non-finite inputs); the generated shortcut
compares `|scalar(b)|` with the norm, so a negative pure scalar takes the
scalar path (Julia's `expm1(Spinor(-2.0))` returns `0`, item 13); the generated
`cosh`/`sinh`, which throw `UndefVarError` in Julia 0.8.46 (item 3), follow
their evident intent.
-/
import Grassmann.Composite.Scalar

namespace Grassmann.Composite

open DirectSum StaticVectors AbstractTensors JuliaBase

/-- The fuel of the loops without a cap (the cap of Julia's generated loops). -/
def seriesFuel : Nat := 10000

/-- The cap `k ≤ 10000` of Julia's generated loops. -/
def seriesCap : Nat := 10000

/-- "No cap" for the generic loops (the fuel still bounds them). -/
def noCap : Nat := 1 <<< 62

/-- Julia's series loop (module docstring): `S` the partial sum, `term` the next term,
`n1 n2 n3` the running norms, `k` the current index (stepping by `dk`, stopping past
`cap`), `step term k` the next term. -/
@[specialize] def seriesLoop {X : Type} (add : X → X → X) (norm : X → Float)
    (step : X → Nat → X) (cap dk : Nat) (S term : X) (n1 n2 n3 : Float) (k : Nat) : Nat → X
  | 0 => S
  | fuel + 1 =>
    if (n2 < n1 || n2 > f1) && k ≤ cap then
      let S := add S term
      let ns := norm S
      if approx ns n3 then S
      else
        let term := step term k
        seriesLoop add norm step cap dk S term n2 (norm term) ns (k + dk) fuel
    else S

/-- The loop of Grassmann's `qlog` (`C:303-321`): `prod` holds `w^(k-2)`, the term is
`prod/k`, and `k` steps by 2 up to `x`. -/
@[specialize] def qlogLoop {X : Type} (add : X → X → X) (mul : X → X → X) (sdiv : X → Float → X)
    (norm : X → Float) (w2 : X) (x : Nat) (S prod term : X) (n1 n2 n3 : Float) (k : Nat) :
    Nat → X
  | 0 => S
  | fuel + 1 =>
    if (n2 < n1 || n2 > f1) && k ≤ x then
      let S := add S term
      let ns := norm S
      if approx ns n3 then S
      else
        let prod := mul prod w2
        let term := sdiv prod (natF k)
        qlogLoop add mul sdiv norm w2 x S prod term n2 (norm term) ns (k + 2) fuel
    else S

/-- Grassmann's `qlog(w, x = 10000)` (`C:303-321`, after Cephes `qlog`) over a carrier:
`2(w + w³/3 + w⁵/5 + …)` = `2 atanh w`, the series of `log((1+w)/(1-w))`, with the
series stopping rule and the term cap `k ≤ x`. (`AbstractTensors.Generic.qlog` is the
same loop for `SeriesRing` carriers.) -/
@[specialize] def qlogWith {X : Type} (add : X → X → X) (mul : X → X → X) (sdiv : X → Float → X)
    (smul : Float → X → X) (norm : X → Float) (w : X) (x : Nat := 10000) : X :=
  let w2 := mul w w
  let f := norm w
  let prod := mul w w2
  let term := sdiv prod f3
  smul f2 (qlogLoop add mul sdiv norm w2 x w prod term f (norm term) f 5 (x / 2 + 1))

/-! ## The carrier-independent series -/

section Generic

variable {X : Type} (add : X → X → X) (mul : X → X → X) (sdiv : X → Float → X) (norm : X → Float)

/-- Grassmann's generic `expm1(t)` (`C:31-51`): `S = t`, `term = t⟑t/2`, next term
`term ⟑ (t/k)` from `k = 3`, `norms = (‖t‖, ‖term‖, ‖t‖)`. -/
@[specialize] def expm1Generic (t : X) : X :=
  let term := sdiv (mul t t) f2
  let f := norm t
  seriesLoop add norm (fun term k => mul term (sdiv t (natF k))) noCap 1 t term f (norm term) f 3
    seriesFuel

/-- The sum `τ/2 + τ²/4! + …` of Grassmann's generic `cosh(t)` (`C:458-481`) from
`τ = t⟑t`: `S = τ/2`, `term = τ⟑τ/24`, next term `term ⟑ (τ/(k(k-1)))` from `k = 6`
(step 2), `norms = (‖S‖, ‖term‖, ‖S‖)`. `cosh t` is `1 +` this. -/
@[specialize] def coshGenericTail (τ : X) : X :=
  let S := sdiv τ f2
  let term := sdiv (mul τ τ) f24
  let f := norm S
  seriesLoop add norm (fun term k => mul term (sdiv τ (natF (k * (k - 1))))) noCap 2 S term
    f (norm term) f 6 seriesFuel

/-- Grassmann's generic `sinh(t)` (`C:517-539`) from `t` and `τ = t⟑t`, where `tτ`
multiplies by `τ` on the right (the carrier of `t` need not contain `τ`: an odd chain
times an even spinor): `S = t`, `term = t⟑τ/6`, next term `term ⟑ (τ/(k(k-1)))` from
`k = 5` (step 2), `norms = (‖t‖, ‖term‖, ‖t‖)`. -/
@[specialize] def sinhGenericWith (mulτ : X → X) (sdivτ : Nat → X → X) (t : X) : X :=
  let f := norm t
  let term := sdiv (mulτ t) f6
  seriesLoop add norm (fun term k => sdivτ (k * (k - 1)) term) noCap 2 t term f (norm term) f 5
    seriesFuel

/-- Grassmann's generated `expm1(b)` for `Multivector`/`Spinor` (`C:54-81`) after its
scalar shortcut: `S = b`, `out = b⟑b/2`, next term `(out/k) ⟑ b` from `k = 3`,
`norms = (‖b‖, ‖out‖, 0)`, cap `k ≤ 10000`. -/
@[specialize] def expm1Generated (b : X) : X :=
  let out := sdiv (mul b b) f2
  seriesLoop add norm (fun out k => mul (sdiv out (natF k)) b) seriesCap 1 b out (norm b) (norm out)
    f0 3 seriesFuel

/-- The sum of Grassmann's generated `cosh(b)` (`C:483-513`) from `τ = b⟑b`: `S = τ/2`,
`out = τ⟑τ/24`, next term `(out/(k(k-1))) ⟑ τ` from `k = 6` (step 2),
`norms = (‖S‖, ‖out‖, 0)`, cap `k ≤ 10000`. `cosh b` is `1 +` this. -/
@[specialize] def coshGeneratedTail (τ : X) : X :=
  let S := sdiv τ f2
  let out := sdiv (mul τ τ) f24
  seriesLoop add norm (fun out k => mul (sdiv out (natF (k * (k - 1)))) τ) seriesCap 2 S out
    (norm S) (norm out) f0 6 seriesFuel

/-- Grassmann's generated `sinh(b)` (`C:541-570`) from `b` and a right multiplication
`mulτ` by `τ = b⟑b` (heterogeneous: `b` may be odd): `S = b`, `out = b⟑τ/6`, next term
`(out/(k(k-1))) ⟑ τ` from `k = 5` (step 2), `norms = (‖b‖, ‖out‖, 0)`, cap. -/
@[specialize] def sinhGeneratedWith (mulτ : X → X) (b : X) : X :=
  let out := sdiv (mulτ b) f6
  seriesLoop add norm (fun out k => mulτ (sdiv out (natF (k * (k - 1))))) seriesCap 2 b out
    (norm b) (norm out) f0 5 seriesFuel

end Generic

/-! ## Integer powers (`src/algebra.jl:440-470`) -/

/-- `out ⟑ v` repeated `k` times (Julia's loop for `i < 8`, starting from `One(V)`). -/
@[specialize] def powRepLoop {X : Type} (mul : X → X → X) (v out : X) : Nat → X
  | 0 => out
  | k + 1 => powRepLoop mul v (mul out v) k

/-- Julia's binary powering for `i ≥ 8`: for the bit positions `j = 1 … K` of `i`
(`K` the highest), `out *= p` when bit `j` is set and `p *= p` unless `j = K`. -/
@[specialize] def powBinLoop {X : Type} (mul : X → X → X) (k : Nat) (out p : X) (j K : Nat) :
    Nat → X
  | 0 => out
  | fuel + 1 =>
    let out := if (k >>> (j - 1)) % 2 == 1 then mul out p else out
    if j ≥ K then out else powBinLoop mul k out (mul p p) (j + 1) K fuel

/-- Grassmann's `v ^ i` for `i ≥ 0` and a non-`Chain`, non-elliptic-`Couple` element
(`src/algebra.jl:440-470`): `v` for `i = 1`; for `i < 8` the product
`((One ⟑ v) ⟑ v) ⟑ …`; otherwise binary powering over the bits of `i` (Julia's exact
multiplication order). -/
@[specialize] def powJulia {X : Type} (mul : X → X → X) (one v : X) (k : Nat) : X :=
  if k == 1 then v
  else if k < 8 then powRepLoop mul v one k
  else
    let K := Nat.log2 k + 1
    powBinLoop mul k one v 1 K (K + 1)

end Grassmann.Composite
