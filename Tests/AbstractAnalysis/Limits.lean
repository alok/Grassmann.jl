import AbstractAnalysis
import Tests.AbstractAnalysis.Harness

/-!
Oracle tests for `Limit`, orbits, sums, products and series
(`oracle/golden/abstractanalysis/limits.json`).

Cases flagged `libm` iterate a transcendental function (Julia's own `cos` vs
the C library's): values then compare to `1e-12` and converged iteration
counts to within two steps; everything else is compared bit-for-bit,
including the printed `show` strings.
-/

open Lean AbstractAnalysis Tests.Golden

namespace Tests.AbstractAnalysis.Limits

/-- Values that can be compared with a golden entry. -/
class GoldenVal (V : Type) where
  /-- Is `v` equal (or within `rtol`) to the golden `j`? -/
  close : V → Json → Float → Bool

instance : GoldenVal Float where
  close v j rtol := let e := jFloat j; sameFloat v e || (v - e).abs ≤ rtol * max v.abs e.abs

instance : GoldenVal FloatArray where
  close v j rtol :=
    let e := jFloats j
    v.size == e.size && (List.range e.size).all fun i =>
      let a := v[i]!; let b := e[i]!; sameFloat a b || (a - b).abs ≤ rtol * max a.abs b.abs

instance : GoldenVal Int where
  close v j _ := v == jInt j

/-- Compare a `Limit` with a golden record `{show, n, r, first, last}`. -/
def limCheck {S V : Type} [JuliaRepr V] [GoldenVal V] (name : String) (L : Limit S V) (rec : Json)
    (rtol : Float := 0) (nSlack : Nat := 0) : TestM Unit := do
  let n := jNat (jGet rec "n")
  check s!"{name}.n" (((L.n : Int) - n).natAbs ≤ nSlack) s!"got {L.n}, expected {n}"
  check s!"{name}.last" (GoldenVal.close L.last (jGet rec "last") rtol) s!"got {JuliaRepr.repr L.last}"
  check s!"{name}.first" (GoldenVal.close L.first (jGet rec "first") rtol) s!"got {JuliaRepr.repr L.first}"
  if rtol == 0 then
    checkFloat s!"{name}.r" L.r (jFloat (jGet rec "r"))
    checkEq s!"{name}.show" L.toJulia (jStr (jGet rec "show"))
    checkEq s!"{name}.compact" (L.toJulia (compact := true)) (jStr (jGet rec "compact"))
  else
    let r := jFloat (jGet rec "r")
    -- a converged residual is tiny and noisy: compare its scale only
    check s!"{name}.r" (sameFloat L.r r || (L.r - r).abs ≤ max (1e-6 * r.abs) 1e-14) s!"got {L.r}, expected {r}"

/-- `v ↦ v / 2` on packed vectors. -/
def halve (v : FloatArray) : FloatArray := ⟨v.data.map (· / 2)⟩

/-- The 2×2 contraction of the generator, written out as Julia does. -/
def contraction (v : FloatArray) : FloatArray :=
  ⟨#[0.5 * v[0]! + 0.2 * v[1]!, 0.1 * v[0]! + 0.3 * v[1]!]⟩

/-- Julia's `Float64^Int` for the series cases (compared with a tolerance). -/
def powi (x : Float) (i : Nat) : Float := x ^ Float.ofNat i

/-- Checks for one scalar map. -/
def scalarMap (name : String) (f : Float → Float) (x0 : Float) (j : Json) (libm : Bool) : TestM Unit := do
  let rtol := if libm then 1e-12 else 0
  limCheck s!"{name}.orbit" (orbit f x0 (d := dist)) (jGet j "orbit") rtol (if libm then 2 else 0)
  for k in [1, 5, 10] do
    limCheck s!"{name}.orbit{k}" (orbitN f x0 k dist) (jGet (jGet j "orbitN") (toString k)) rtol
  limCheck s!"{name}.fixedcycle10" ((FixedCycle.mk 10 f dist).run x0) (jGet j "fixedcycle10") rtol
  let (_, errs) := orbitError f x0 (d := dist)
  let exp := jFloats (jGet j "orbiterror")
  if libm then
    check s!"{name}.orbiterror.len" (((errs.size : Int) - exp.size).natAbs ≤ 2)
  else
    check s!"{name}.orbiterror" (GoldenVal.close errs (jGet j "orbiterror") 0)
  check s!"{name}.collect5" (GoldenVal.close (⟨(orbitN f x0 5 dist).collect⟩ : FloatArray) (jGet j "collect5") rtol)

/-- Checks for one vector map. -/
def vectorMap (name : String) (f : FloatArray → FloatArray) (x0 : FloatArray) (j : Json) : TestM Unit := do
  limCheck s!"{name}.orbit" (orbit f x0 (d := dist)) (jGet j "orbit")
  for k in [1, 5, 10] do
    limCheck s!"{name}.orbit{k}" (orbitN f x0 k dist) (jGet (jGet j "orbitN") (toString k))
  limCheck s!"{name}.fixedcycle10" ((FixedCycle.mk 10 f dist).run x0) (jGet j "fixedcycle10")
  let (_, errs) := orbitError f x0 (d := dist)
  check s!"{name}.orbiterror" (GoldenVal.close errs (jGet j "orbiterror") 0)
  let col := (orbitN f x0 5 dist).collect
  let exp := jArr (jGet j "collect5")
  check s!"{name}.collect5" (col.size == exp.size && (List.range exp.size).all fun i =>
    GoldenVal.close col[i]! exp[i]! 0)

/-- Checks for one countable sequence. -/
def countable (name : String) (f : Nat → Float) (j : Json) : TestM Unit := do
  let x : CountableVector Float := ⟨f, 10⟩
  let S := x.sum
  let P := x.prod
  check s!"{name}.terms" (GoldenVal.close (⟨(x.slice 1 12)⟩ : FloatArray) (jGet j "terms") 0)
  limCheck s!"{name}.sum" S (jGet j "sum")
  limCheck s!"{name}.prod" P (jGet j "prod")
  for k in [1, 9, 10, 13] do limCheck s!"{name}.sum[{k}]" (S.seek k) (jGet (jGet j "sum_seek") (toString k))
  for k in [1, 9, 13] do limCheck s!"{name}.prod[{k}]" (P.seek k) (jGet (jGet j "prod_seek") (toString k))
  if (jGet j "sum_eps4") != .null then limCheck s!"{name}.sum[1e-4]" (S.limitEps 1e-4) (jGet j "sum_eps4")
  if (jGet j "sum_eps8") != .null then limCheck s!"{name}.sum[1e-8]" (S.limitEps 1e-8) (jGet j "sum_eps8")
  limCheck s!"{name}.sum+1" (S + (1 : Float)) (jGet j "sum_plus1")
  limCheck s!"{name}.1-sum" ((1 : Float) - S) (jGet j "one_minus_sum")
  limCheck s!"{name}.2*sum" ((2 : Float) * S) (jGet j "two_times_sum")
  limCheck s!"{name}.sum/2" (S / (2 : Float)) (jGet j "sum_div2")
  limCheck s!"{name}.sum*sum" (S * S) (jGet j "sum_times_sum")
  limCheck s!"{name}.sum+prod" (S + P) (jGet j "sum_plus_prod")
  limCheck s!"{name}.map(2x)" (S.map (2 * ·) dist) (jGet j "map_double")
  limCheck s!"{name}.map(abs)" (S.map Float.abs dist) (jGet j "map_abs")
  check s!"{name}.collect(sum)" (GoldenVal.close (⟨S.collect⟩ : FloatArray) (jGet j "collect_sum") 0)
  check s!"{name}.collect(prod)" (GoldenVal.close (⟨P.collect⟩ : FloatArray) (jGet j "collect_prod") 0)
  limCheck s!"{name}.limit" (x.limit 10 dist) (jGet j "limit")
  limCheck s!"{name}.limit3" (x.limit 3 dist) (jGet j "limit3")
  limCheck s!"{name}.limit(1e-4)" (x.limitEps 1e-4 dist) (jGet j "limit_eps4")
  limCheck s!"{name}.dot" (x.dot x) (jGet j "dot")
  check s!"{name}.cumsum" (GoldenVal.close (⟨x.cumsum.take 12⟩ : FloatArray) (jGet j "cumsum") 0)
  check s!"{name}.cumprod" (GoldenVal.close (⟨x.cumprod.take 12⟩ : FloatArray) (jGet j "cumprod") 0)
  check s!"{name}.supseq3" (GoldenVal.close (⟨(x.supseq 3).slice 1 10⟩ : FloatArray) (jGet j "supseq3") 0)
  check s!"{name}.infseq3" (GoldenVal.close (⟨(x.infseq 3).slice 1 10⟩ : FloatArray) (jGet j "infseq3") 0)
  limCheck s!"{name}.sum(sum)" S.sum (jGet j "sum_of_sum")
  limCheck s!"{name}.prod(sum)" S.prod (jGet j "prod_of_sum")
  limCheck s!"{name}.rerun" (S.rerun ⟨1, 0.5⟩) (jGet j "sum_rerun")

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/abstractanalysis/limits.json"
  for m in jArr (jGet j "maps") do
    let name := jStr (jGet m "name")
    let libm := jBool (jGet m "libm")
    match name with
    | "cos" => scalarMap name Float.cos 1.0 m libm
    | "half_plus_one" => scalarMap name (fun x => x / 2 + 1) 0.0 m libm
    | "babylonian" => scalarMap name (fun x => (x + 2 / x) / 2) 1.0 m libm
    | "newton3" => scalarMap name (fun x => x - (x * x - 3) / (2 * x)) 1.0 m libm
    | "logistic" => scalarMap name (fun x => 2.5 * x * (1 - x)) 0.5 m libm
    | "contraction" => vectorMap name contraction ⟨#[1.0, 2.0]⟩ m
    | "halve_vec" => vectorMap name halve ⟨#[1.0, 2.0]⟩ m
    | other => check s!"unknown map {other}" false
  limCheck "orbithold" (orbitHold (fun x y => (y + x / y) / 2) 2.0 6 dist) (jGet j "orbithold")
  for c in jArr (jGet j "countable") do
    let name := jStr (jGet c "name")
    match name with
    | "inv_sq" => countable name (fun i => 1 / Float.ofNat (i * i)) c
    | "alt_harmonic" => countable name (fun i => (if i % 2 == 0 then 1.0 else -1.0) / Float.ofNat i) c
    | "inv_pow2" => countable name (fun i => 1 / Float.ofNat (2 ^ i)) c
    | "one_plus_inv_sq" => countable name (fun i => 1 + 1 / Float.ofNat (i * i)) c
    | other => check s!"unknown countable {other}" false
  let s := jGet j "series"
  limCheck "series(x^i)(0.5)" ((FunctionVector.series ⟨fun x i => powi x i, 5⟩).eval 0.5) (jGet s "series_pow_0.5")
  limCheck "series(x^i)(0.3)" ((FunctionVector.series ⟨fun x i => powi x i, 5⟩).eval 0.3)
    (jGet s "series_pow_0.3") 1e-15
  limCheck "product(1+x^i)(0.5)" ((FunctionVector.product ⟨fun x i => 1 + powi x i, 4⟩).eval 0.5)
    (jGet s "product_0.5")
  limCheck "product(1+x^i)(0.3)" ((FunctionVector.product ⟨fun x i => 1 + powi x i, 4⟩).eval 0.3)
    (jGet s "product_0.3") 1e-15
  for n in [10, 20, 25] do
    limCheck s!"prod(Naturals({n}))" (prodNaturals n) (jGet s s!"prod_naturals_{n}")

end Tests.AbstractAnalysis.Limits
