import JuliaBase

/-!
# Butcher and Adams tables (Adapode.jl `src/constants.jl`)

Adapode's integrators read four tables (`src/constants.jl:5-99`):

| Julia | Lean | content |
|---|---|---|
| `CB[o]`, `o = 1…4` (`constants.jl:5-20`) | `CB o` | explicit Runge–Kutta: Euler, midpoint, Kutta's third order, classical RK4 |
| `CBA[o]`, `o = 1…5` (`constants.jl:22-59`) | `CBA o` | embedded pairs: Heun–Euler, Bogacki–Shampine, Fehlberg, Cash–Karp, Dormand–Prince |
| `CAB[k]`, `k = 1…5` (`constants.jl:61-65`) | `CAB k` | `k`-step Adams–Bashforth weights, oldest value first |
| `CAM[k]`, `k = 1…5` (`constants.jl:67-71`) | `CAM k` | order-`k` Adams–Moulton weights, oldest value first, the last one multiplying `f(tₙ₊₁)` |
| `Gauss[n]`, `n = 1…4` (`constants.jl:73-99`) | `Gauss n` | triangle quadrature (weights summing to 1, points in the reference triangle) |

**Exact data, Julia's floats.** Every entry is written in Julia as a quotient of integers
(`1932/2197`) or a decimal literal equal to one (`0.09375`, `-0.18`), so its `Float64` value is the
correctly rounded rational. The tables are stored here as exact rationals (`Q`), and the `Float`
tables are their correctly rounded values (`Q.toFloat`), bit-identical to Julia's
(`Tests/Adapode/Tables.lean` checks every entry against the oracle). The two derived float
quantities are computed as Julia does: the error weights `db = b - bhat` of an embedded pair
(`constants(a,b,c) = Values(a...,b,b-c)`, `constants.jl:22`) are a `Float` difference of the rounded
weights, and the stage times `cₗ = sum(aₗ)` (`Adapode.jl:272, 286`) are the left-to-right `Float` sum
of the rounded row (StaticVectors' `sum`; e.g. the fifth Dormand–Prince row sums to
`0.8888888888888891`, not `8/9`).

**Order conditions are kernel-checked.** `QTableau.hasOrder p` evaluates the 17 rooted-tree
conditions of order `≤ 5` in exact arithmetic, and the theorems below state the order of every
method by `decide`. They also document the two typos in `constants.jl` (port notes §8.6 B10):

* Fehlberg's `a₆₃` is `+3544/2565` (it should be `-3544/2565`), so the advancing fifth-order weights
  only have order 1 (`fehlberg_julia_order`); the fourth-order weights give `a₆·` weight zero and keep
  their order 4.
* Cash–Karp's `a₄₁` is `3/40` (it should be `3/10`), which breaks both solutions (order 1).

`CBA` reproduces Julia (typos included), because Julia's step sequences are the oracle; the corrected
pairs are `fehlbergFixed` and `cashKarpFixed` (`CBA.fixed`), selected by `ExplicitAdaptor`'s `fixed`
flag.

**Which weights advance.** Adapode advances with `b` and estimates the error with `b - bhat`.
For Heun–Euler, Bogacki–Shampine and Cash–Karp `b` is the *lower*-order solution; for Fehlberg and
Dormand–Prince it is the higher-order one (local extrapolation). `hasOrder` states both.
-/

namespace Adapode

open JuliaBase

/-! ## Exact rationals -/

/-- An exact rational `num / den` (`den > 0`): just the arithmetic the tables and the order
conditions need. Operations reduce by `Nat.gcd`; everything is structural, so the kernel evaluates it
(the order theorems are proved by `decide`). -/
structure Q where
  /-- Numerator. -/
  num : Int
  /-- Denominator (positive). -/
  den : Nat := 1
  deriving Repr, Inhabited

namespace Q

/-- `n / d` in lowest terms. -/
def mk' (n : Int) (d : Nat) : Q :=
  let g := Nat.gcd n.natAbs d
  if g ≤ 1 then ⟨n, d⟩ else ⟨n / (g : Int), d / g⟩

instance {n : Nat} : OfNat Q n := ⟨⟨n, 1⟩⟩
instance : Add Q := ⟨fun a b => mk' (a.num * b.den + b.num * a.den) (a.den * b.den)⟩
instance : Mul Q := ⟨fun a b => mk' (a.num * b.num) (a.den * b.den)⟩
instance : Neg Q := ⟨fun a => ⟨-a.num, a.den⟩⟩
instance : Sub Q := ⟨fun a b => a + -b⟩

/-- Equality of values (cross-multiplication; representations need not be reduced). -/
def beq (a b : Q) : Bool := a.num * b.den == b.num * a.den

instance : BEq Q := ⟨beq⟩

/-- Julia `n/d` for integers `n`, `d` (`Float64(n)/Float64(d)`): the correctly rounded value, since
both conversions are exact for the table entries (`|n|, d < 2^53`). -/
def toFloat (a : Q) : Float := Float.ofInt a.num / Float.ofNat a.den

end Q

/-- `n / d` as a table entry (not reduced: `4/6` stays as Julia writes it). -/
def q (n : Int) (d : Nat := 1) : Q := ⟨n, d⟩

/-- Left-to-right sum of exact values. -/
def qsum (xs : List Q) : Q := xs.foldl (· + ·) 0

/-- `Σ xᵢ yᵢ`. -/
def qdot (xs ys : List Q) : Q := qsum (List.zipWith (· * ·) xs ys)

/-- Componentwise product. -/
def qhad (xs ys : List Q) : List Q := List.zipWith (· * ·) xs ys

/-! ## Exact Butcher tableaux and their order conditions -/

/-- An explicit Runge–Kutta tableau over exact rationals: `a` lists the stage rows `a₁ … a_{s-1}`
(row `l` has `l` entries: stage `l+1` combines stages `1 … l`), `b` the advancing weights and `bhat`
the embedded weights of an adaptive pair (Julia's `constants(a, b, c)` with `c = bhat`), empty for
a fixed-step method. -/
structure QTableau where
  /-- Strictly lower-triangular stage rows. -/
  a : List (List Q)
  /-- Weights of the advancing solution. -/
  b : List Q
  /-- Weights of the embedded (error-estimating) solution; `[]` for fixed-step tableaux. -/
  bhat : List Q := []
  deriving Inhabited

namespace QTableau

/-- The stage times `cᵢ = Σⱼ aᵢⱼ` (`c₁ = 0`). -/
def c (T : QTableau) : List Q := 0 :: T.a.map qsum

/-- `A v`: stage `i` gets `Σⱼ aᵢⱼ vⱼ` (`0` for the first stage). -/
def mulA (T : QTableau) (v : List Q) : List Q := 0 :: T.a.map (fun row => qdot row v)

/-- `(φ, 1/γ)` for every rooted tree `t` with `|t| ≤ 5`, grouped by order (1, 1, 2, 4, 9 trees): a
tableau with weights `w` has order `p` iff `w · φ(t) = 1/γ(t)` for every tree with `|t| ≤ p`
(Butcher). Entries are `(order, φ, 1/γ)`. -/
def trees (T : QTableau) : List (Nat × List Q × Q) :=
  let c := T.c
  let one := c.map fun _ => (1 : Q)
  let A := T.mulA
  let c2 := qhad c c
  let c3 := qhad c2 c
  let Ac := A c
  let Ac2 := A c2
  let AAc := A Ac
  [ (1, one, 1),
    (2, c, q 1 2),
    (3, c2, q 1 3), (3, Ac, q 1 6),
    (4, c3, q 1 4), (4, qhad c Ac, q 1 8), (4, Ac2, q 1 12), (4, AAc, q 1 24),
    (5, qhad c3 c, q 1 5), (5, qhad c2 Ac, q 1 10), (5, qhad Ac Ac, q 1 20), (5, qhad c Ac2, q 1 15),
    (5, qhad c AAc, q 1 30), (5, A c3, q 1 20), (5, A (qhad c Ac), q 1 40), (5, A Ac2, q 1 60),
    (5, A AAc, q 1 120) ]

/-- Whether the weights `w` give order `≥ p` (`p ≤ 5`) with the stage rows of `T`. -/
def orderOf (T : QTableau) (w : List Q) (p : Nat) : Bool :=
  T.trees.all fun (k, φ, g) => p < k || qdot w φ == g

/-- The advancing solution has order `≥ p`. -/
def hasOrder (T : QTableau) (p : Nat) : Bool := T.orderOf T.b p

/-- The embedded solution has order `≥ p`. -/
def embeddedOrder (T : QTableau) (p : Nat) : Bool := T.orderOf T.bhat p

/-- Every row sums to its stage time and the rows have the right lengths (`a₁` has one entry, …). -/
def wellShaped (T : QTableau) : Bool :=
  (T.a.zipIdx.all fun (row, l) => row.length == l + 1) &&
    T.b.length == T.a.length + 1 && (T.bhat.isEmpty || T.bhat.length == T.b.length)

end QTableau

/-! ### The tables of `constants.jl`, exactly -/

/-- `CB[1]`: explicit Euler (`constants.jl:6-8`). -/
def cb1 : QTableau := { a := [], b := [q 1] }
/-- `CB[2]`: the explicit midpoint rule (`constants.jl:9-11`). -/
def cb2 : QTableau := { a := [[q 1 2]], b := [q 0, q 1] }
/-- `CB[3]`: Kutta's third-order method (`constants.jl:12-15`); `(1,4,1)./6`. -/
def cb3 : QTableau := { a := [[q 1 2], [q (-1), q 2]], b := [q 1 6, q 4 6, q 1 6] }
/-- `CB[4]`: the classical Runge–Kutta method (`constants.jl:16-20`); `(1,2,2,1)./6`. -/
def cb4 : QTableau :=
  { a := [[q 1 2], [q 0, q 1 2], [q 0, q 0, q 1]], b := [q 1 6, q 2 6, q 2 6, q 1 6] }

/-- `CBA[1]`: Heun–Euler (`constants.jl:25-28`): advances with Euler, estimates with Heun. -/
def heunEuler : QTableau := { a := [[q 1]], b := [q 1, q 0], bhat := [q 1 2, q 1 2] }

/-- `CBA[2]`: Bogacki–Shampine (`constants.jl:29-34`): advances with the second-order weights. -/
def bogackiShampine : QTableau :=
  { a := [[q 1 2], [q 0, q 3 4], [q 2 9, q 3 9, q 4 9]],
    b := [q 7 24, q 1 4, q 1 3, q 1 8], bhat := [q 2 9, q 1 3, q 4 9, q 0] }

/-- The Fehlberg stage rows with the sign of `a₆₃` as given. -/
def fehlbergRows (a63 : Q) : List (List Q) :=
  [[q 1 4], [q 3 32, q 9 32], [q 1932 2197, q (-7200) 2197, q 7296 2197],
   [q 439 216, q (-8), q 3680 513, q (-845) 4104], [q (-8) 27, q 2, a63, q 1859 4104, q (-11) 40]]

/-- `CBA[3]` as Julia has it (`constants.jl:35-42`), with the typo `a₆₃ = +3544/2565`; advances with
the fifth-order weights (`0.09375 = 3/32`, `0.28125 = 9/32`, `-0.18 = -9/50`, `-0.2 = -1/5`). -/
def fehlbergJulia : QTableau :=
  { a := fehlbergRows (q 3544 2565),
    b := [q 16 135, q 0, q 6656 12825, q 28561 56430, q (-9) 50, q 2 55],
    bhat := [q 25 216, q 0, q 1408 2565, q 2197 4104, q (-1) 5, q 0] }

/-- Runge–Kutta–Fehlberg 4(5) with the published `a₆₃ = -3544/2565`. -/
def fehlbergFixed : QTableau := { fehlbergJulia with a := fehlbergRows (q (-3544) 2565) }

/-- The Cash–Karp stage rows with `a₄₁` as given. -/
def cashKarpRows (a41 : Q) : List (List Q) :=
  [[q 1 5], [q 3 40, q 9 40], [a41, q (-9) 10, q 6 5], [q (-11) 54, q 5 2, q (-70) 27, q 35 27],
   [q 1631 55296, q 175 512, q 575 13824, q 44275 110592, q 253 4096]]

/-- `CBA[4]` as Julia has it (`constants.jl:43-50`), with the typo `a₄₁ = 3/40`; advances with the
fourth-order weights (`0.25 = 1/4`). -/
def cashKarpJulia : QTableau :=
  { a := cashKarpRows (q 3 40),
    b := [q 2825 27648, q 0, q 18575 48384, q 13525 55296, q 277 14336, q 1 4],
    bhat := [q 37 378, q 0, q 250 621, q 125 594, q 0, q 512 1771] }

/-- Cash–Karp 4(5) with the published `a₄₁ = 3/10`. -/
def cashKarpFixed : QTableau := { cashKarpJulia with a := cashKarpRows (q 3 10) }

/-- `CBA[5]`: Dormand–Prince 5(4) (`constants.jl:51-59`); advances with the fifth-order weights
(the seventh row repeats `b`: first same as last). -/
def dormandPrince : QTableau :=
  { a := [[q 1 5], [q 3 40, q 9 40], [q 44 45, q (-56) 15, q 32 9],
          [q 19372 6561, q (-25360) 2187, q 64448 6561, q (-212) 729],
          [q 9017 3168, q (-355) 33, q 46732 5247, q 49 176, q (-5103) 18656],
          [q 35 384, q 0, q 500 1113, q 125 192, q (-2187) 6784, q 11 84]],
    b := [q 35 384, q 0, q 500 1113, q 125 192, q (-2187) 6784, q 11 84, q 0],
    bhat := [q 5179 57600, q 0, q 7571 16695, q 393 640, q (-92097) 339200, q 187 2100, q 1 40] }

/-! ### Kernel-checked orders -/

theorem cb_wellShaped :
    cb1.wellShaped ∧ cb2.wellShaped ∧ cb3.wellShaped ∧ cb4.wellShaped := by decide +kernel

theorem cba_wellShaped :
    heunEuler.wellShaped ∧ bogackiShampine.wellShaped ∧ fehlbergJulia.wellShaped ∧
      cashKarpJulia.wellShaped ∧ dormandPrince.wellShaped ∧ fehlbergFixed.wellShaped ∧
      cashKarpFixed.wellShaped := by decide +kernel

/-- `CB[o]` has order exactly `o`. -/
theorem cb_order :
    (cb1.hasOrder 1 ∧ !cb1.hasOrder 2) ∧ (cb2.hasOrder 2 ∧ !cb2.hasOrder 3) ∧
      (cb3.hasOrder 3 ∧ !cb3.hasOrder 4) ∧ (cb4.hasOrder 4 ∧ !cb4.hasOrder 5) := by decide +kernel

/-- Heun–Euler advances with Euler (order 1) and estimates with Heun (order 2). -/
theorem heunEuler_order :
    heunEuler.hasOrder 1 ∧ !heunEuler.hasOrder 2 ∧ heunEuler.embeddedOrder 2 ∧
      !heunEuler.embeddedOrder 3 := by decide +kernel

/-- Bogacki–Shampine advances with order 2 and estimates with order 3. -/
theorem bogackiShampine_order :
    bogackiShampine.hasOrder 2 ∧ !bogackiShampine.hasOrder 3 ∧
      bogackiShampine.embeddedOrder 3 ∧ !bogackiShampine.embeddedOrder 4 := by decide +kernel

/-- Dormand–Prince advances with order 5 and estimates with order 4. -/
theorem dormandPrince_order :
    dormandPrince.hasOrder 5 ∧ dormandPrince.embeddedOrder 4 ∧
      !dormandPrince.embeddedOrder 5 := by decide +kernel

/-- Julia's Fehlberg table (typo `a₆₃ = +3544/2565`): the advancing weights drop to order 1, the
embedded fourth-order weights (which give stage 6 weight zero) keep order 4. -/
theorem fehlberg_julia_order :
    fehlbergJulia.hasOrder 1 ∧ !fehlbergJulia.hasOrder 2 ∧ fehlbergJulia.embeddedOrder 4 := by decide +kernel

/-- The published Fehlberg 4(5) pair: advancing order 5, embedded order 4. -/
theorem fehlberg_fixed_order :
    fehlbergFixed.hasOrder 5 ∧ fehlbergFixed.embeddedOrder 4 ∧
      !fehlbergFixed.embeddedOrder 5 := by decide +kernel

/-- Julia's Cash–Karp table (typo `a₄₁ = 3/40`): both solutions drop to order 1. -/
theorem cashKarp_julia_order :
    cashKarpJulia.hasOrder 1 ∧ !cashKarpJulia.hasOrder 2 ∧ cashKarpJulia.embeddedOrder 1 ∧
      !cashKarpJulia.embeddedOrder 2 := by decide +kernel

/-- The published Cash–Karp 4(5) pair: advancing order 4, embedded order 5. -/
theorem cashKarp_fixed_order :
    cashKarpFixed.hasOrder 4 ∧ !cashKarpFixed.hasOrder 5 ∧ cashKarpFixed.embeddedOrder 5 := by decide +kernel

/-! ### Adams weights -/

/-- `CAB[k]` (`constants.jl:61-65`), oldest value first. -/
def cabQ : Nat → List Q
  | 1 => [q 1]
  | 2 => [q (-1) 2, q 3 2]
  | 3 => [q 5 12, q (-16) 12, q 23 12]
  | 4 => [q (-9) 24, q 37 24, q (-59) 24, q 55 24]
  | _ => [q 251 720, q (-1274) 720, q 2616 720, q (-2774) 720, q 1901 720]

/-- `CAM[k]` (`constants.jl:67-71`), oldest value first; the last weight multiplies `f(tₙ₊₁)`. -/
def camQ : Nat → List Q
  | 1 => [q 1]
  | 2 => [q 1 2, q 1 2]
  | 3 => [q (-1) 12, q 8 12, q 5 12]
  | 4 => [q 1 24, q (-5) 24, q 19 24, q 9 24]
  | _ => [q (-19) 720, q 106 720, q (-264) 720, q 646 720, q 251 720]

/-- `∫₀¹ s^m ds = Σⱼ wⱼ (nⱼ)^m` for `m < k`: the weights `w` on the nodes `n₀, n₀+1, …` integrate
polynomials of degree `< k` exactly over one step (the Adams order conditions). -/
def adamsExact (w : List Q) (n₀ : Int) (k : Nat) : Bool :=
  (List.range k).all fun m =>
    qsum (w.zipIdx.map fun (x, j) => x * ⟨(n₀ + j) ^ m, 1⟩) == q 1 (m + 1)

/-- `CAB[k]` is the `k`-step Adams–Bashforth method (nodes `-(k-1) … 0`, exact to degree `k-1`) and
`CAM[k]` the order-`k` Adams–Moulton method (nodes `-(k-2) … 1`). -/
theorem adams_order :
    (List.range 5).all (fun i => let k := i + 1
      adamsExact (cabQ k) (1 - k) k && !adamsExact (cabQ k) (1 - k) (k + 1) &&
      adamsExact (camQ k) (2 - k) k && !adamsExact (camQ k) (2 - k) (k + 1)) := by decide +kernel

/-! ## Float tables (Julia's `Float64` values) -/

/-- A `FloatArray` of correctly rounded rationals. -/
def floats (xs : List Q) : FloatArray := ⟨(xs.map Q.toFloat).toArray⟩

/-- Julia's left-to-right `sum` of a row of `Float`s (StaticVectors' `sum`). -/
def fsum (xs : List Float) : Float :=
  match xs with
  | [] => 0
  | x :: rest => rest.foldl (· + ·) x

/-- An explicit Runge–Kutta tableau in Julia's `Float64` values, flat for the stepping loops:
stage row `l` (`l = 1 … s-1`, 1-based; it has `l` entries) starts at `a[l(l-1)/2]`. -/
structure Tableau where
  /-- Number of stages `s`. -/
  s : Nat
  /-- The stage rows, flattened. -/
  a : FloatArray
  /-- Stage times `c[l] = sum(aₗ)` (Julia's `Float` sum of the rounded row), `c[0] = 0`. -/
  c : FloatArray
  /-- Advancing weights (`s` entries). -/
  b : FloatArray
  /-- Error weights `b - bhat` as Julia computes them (`Float` difference); empty for `CB`. -/
  db : FloatArray
  deriving Inhabited

/-- The `Float` tableau of exact data. -/
def Tableau.ofQ (T : QTableau) : Tableau :=
  let rows := T.a.map fun r => r.map Q.toFloat
  let b := T.b.map Q.toFloat
  let db := List.zipWith (· - ·) b (T.bhat.map Q.toFloat)
  { s := T.b.length, a := ⟨rows.flatten.toArray⟩, c := ⟨(0 :: rows.map fsum).toArray⟩,
    b := ⟨b.toArray⟩, db := ⟨db.toArray⟩ }

/-- Julia `CB[1]` … `CB[4]` in `Float64` (explicit Euler, midpoint, Kutta 3, RK4). -/
def cbTable1 : Tableau := .ofQ cb1
/-- Julia `CB[2]`. -/
def cbTable2 : Tableau := .ofQ cb2
/-- Julia `CB[3]`. -/
def cbTable3 : Tableau := .ofQ cb3
/-- Julia `CB[4]`. -/
def cbTable4 : Tableau := .ofQ cb4

/-- Julia `CB[o]` (`o = 1 … 4`; larger `o` give RK4). -/
def CB : Nat → Tableau
  | 1 => cbTable1
  | 2 => cbTable2
  | 3 => cbTable3
  | _ => cbTable4

/-- Julia `CBA[1]` … `CBA[5]` in `Float64`. -/
def cbaTable1 : Tableau := .ofQ heunEuler
/-- Julia `CBA[2]`. -/
def cbaTable2 : Tableau := .ofQ bogackiShampine
/-- Julia `CBA[3]` (typo included). -/
def cbaTable3 : Tableau := .ofQ fehlbergJulia
/-- Julia `CBA[4]` (typo included). -/
def cbaTable4 : Tableau := .ofQ cashKarpJulia
/-- Julia `CBA[5]`. -/
def cbaTable5 : Tableau := .ofQ dormandPrince
/-- The corrected Fehlberg pair. -/
def cbaTable3Fixed : Tableau := .ofQ fehlbergFixed
/-- The corrected Cash–Karp pair. -/
def cbaTable4Fixed : Tableau := .ofQ cashKarpFixed

/-- Julia `CBA[o]` (`o = 1 … 5`; larger `o` give Dormand–Prince), typos included. -/
def CBA : Nat → Tableau
  | 1 => cbaTable1
  | 2 => cbaTable2
  | 3 => cbaTable3
  | 4 => cbaTable4
  | _ => cbaTable5

/-- `CBA` with the Fehlberg and Cash–Karp typos corrected (B10). -/
def CBA.fixed : Nat → Tableau
  | 3 => cbaTable3Fixed
  | 4 => cbaTable4Fixed
  | o => CBA o

/-- Julia `CAB[1]` … `CAB[5]` in `Float64`. -/
def cabTable1 : FloatArray := floats (cabQ 1)
/-- Julia `CAB[2]`. -/
def cabTable2 : FloatArray := floats (cabQ 2)
/-- Julia `CAB[3]`. -/
def cabTable3 : FloatArray := floats (cabQ 3)
/-- Julia `CAB[4]`. -/
def cabTable4 : FloatArray := floats (cabQ 4)
/-- Julia `CAB[5]`. -/
def cabTable5 : FloatArray := floats (cabQ 5)

/-- Julia `CAB[k]` (`k = 1 … 5`), oldest value first. -/
def CAB : Nat → FloatArray
  | 1 => cabTable1
  | 2 => cabTable2
  | 3 => cabTable3
  | 4 => cabTable4
  | _ => cabTable5

/-- Julia `CAM[1]` … `CAM[5]` in `Float64`. -/
def camTable1 : FloatArray := floats (camQ 1)
/-- Julia `CAM[2]`. -/
def camTable2 : FloatArray := floats (camQ 2)
/-- Julia `CAM[3]`. -/
def camTable3 : FloatArray := floats (camQ 3)
/-- Julia `CAM[4]`. -/
def camTable4 : FloatArray := floats (camQ 4)
/-- Julia `CAM[5]`. -/
def camTable5 : FloatArray := floats (camQ 5)

/-- Julia `CAM[k]` (`k = 1 … 5`), oldest value first. -/
def CAM : Nat → FloatArray
  | 1 => camTable1
  | 2 => camTable2
  | 3 => camTable3
  | 4 => camTable4
  | _ => camTable5

/-! ## Triangle quadrature (`Gauss`, `constants.jl:73-99`) -/

/-- A quadrature rule on the reference triangle `{(r, s) : r, s ≥ 0, r + s ≤ 1}`: weights summing
to (about) 1 (the finite-element code divides by 2 for the area) and the points `(rᵢ, sᵢ)`. -/
structure TriangleRule where
  /-- Weights. -/
  w : FloatArray
  /-- `r` coordinates of the points. -/
  r : FloatArray
  /-- `s` coordinates of the points. -/
  s : FloatArray
  deriving Inhabited

/-- A rule from exact data: weights and `(r, s)` pairs. -/
def TriangleRule.ofQ (w : List Q) (pts : List (Q × Q)) : TriangleRule :=
  ⟨floats w, floats (pts.map (·.1)), floats (pts.map (·.2))⟩

/-- Julia `Gauss[1]`: the centroid rule. -/
def gauss1 : TriangleRule := .ofQ [q 1] [(q 1 3, q 1 3)]
/-- Julia `Gauss[2]`: three points `(1,1)/6, (4,1)/6, (1,4)/6`. -/
def gauss2 : TriangleRule :=
  .ofQ [q 1 3, q 1 3, q 1 3] [(q 1 6, q 1 6), (q 4 6, q 1 6), (q 1 6, q 4 6)]
/-- Julia `Gauss[3]`: Strang–Fix's four-point rule with a negative centroid weight. -/
def gauss3 : TriangleRule :=
  .ofQ [q (-27) 48, q 25 48, q 25 48, q 25 48]
    [(q 1 3, q 1 3), (q 1 5, q 1 5), (q 3 5, q 1 5), (q 1 5, q 3 5)]
/-- Julia `Gauss[4]`: the six-point degree-4 rule, with Julia's rational approximations of the
weights and points (`35494641/158896895`, …; the weights sum to `0.9999999999999991`). -/
def gauss4 : TriangleRule :=
  let a := q 100320057 224958844
  let b := q 16300311 150784976
  let c := q 13196394 144102857
  let d := q 85438943 104595944
  let w1 := q 35494641 158896895
  let w2 := q 40960013 372527180
  .ofQ [w1, w1, w1, w2, w2, w2] [(a, a), (a, b), (b, a), (c, c), (c, d), (d, c)]

/-- Julia `Gauss[n]` (`n = 1 … 4`). -/
def Gauss : Nat → TriangleRule
  | 1 => gauss1
  | 2 => gauss2
  | 3 => gauss3
  | _ => gauss4

end Adapode
