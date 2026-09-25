import Tests.Forms.Common
import Grassmann.Calculus
import Grassmann.Calculus.Simplicial

/-!
# `Grassmann.Calculus` against Julia

Golden `oracle/golden/forms/calculus.json` (`oracle/forms/gen_calculus.jl`), every result the
dense coefficients of Julia's `Multivector(result)`:

* `plain`: `V(∇)` and, for random chains of every grade and random multivectors of `S"++"`,
  `S"+++"`, `S"++++"`, `S"-+++"`, `S"∞∅++"`: `∂`, `d`, `δ`, `gradient`, `divergence`, `curl`.
  Where Julia throws (`∂` of a scalar, `d`/`gradient`/`curl` of a top-grade chain: a
  `MethodError` in the generated product; `δ` of a zero boundary: `-(::Zero)`) the result
  here is zero, which is checked.
* `simplices`: `∂(ω) = ∧(ω)⋅Λ(W).v1` of random vertex operators (`m` points of `W`, `m ≤ W`),
  through `simplexBoundary` and the `∂` notation.
* `tangent`: `V(∇) = Σₖ ∂ₖvₖ` of `tangent(ℝⁿ, μ, ν)` and, for chains of the non-tangent
  generators, `∂`, `d`, `⋆d` through `nablaM` (the Julia entries with symbolic coefficients,
  recorded as errors of `Float64(::Multivector)`, are skipped).

`rtol = 1e-12`: the operators are sums of products by `±1`, in Julia's product kernels' order
up to the order of the terms.
-/

namespace Tests.FormsTests.CalculusSuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests Grassmann.Calculus

/-- The comparison mode. -/
def m : Mode := .approx 1e-12

/-- Dense coefficients as scalars. -/
def dense {V : TensorBundle} (x : Multivector V Float) : List Num := x.v.toList.map .flt

/-- Compare with a golden dense vector; a Julia error expects zero (the defects fixed here). -/
def expectOrZero {V : TensorBundle} (t : Tally) (got : Multivector V Float) (want : Json)
    (what : Unit → String) : Tally :=
  if (jerr? want).isSome then
    t.ok (got.v.toList.all (· == 0)) fun _ => s!"{what ()}: Julia throws, want zero, got {got.v.toList}"
  else t.nums m (dense got) want what

/-- One `plain` case in the space `V`. -/
def plainIn (V : TensorBundle) [Kernels V] (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let what := (fld c "what").getStr?.toOption.getD ""
  let w := fun (s : String) => fun (_ : Unit) => s!"plain case {k} {V} {what} {s}"
  let mut t := t
  if what == "nabla" then
    t := t.nums m (dense (toMultivector (nabla V Float))) (fld c "out") (w "V(∇)")
    t := t.nums m (dense (nablaM V Float)) (fld c "out") (w "nablaM")
    t := t.nums m (dense (toMultivector (∇ : Chain V 1 Float))) (fld c "out") (w "∇")
  else if what == "chain" then
    let g := (fld c "grade").getNat?.toOption.getD 0
    let ω : Chain V g Float := chainOf V g (flts (fld c "x"))
    t := expectOrZero t (toMultivector (boundary ω)) (fld c "boundary") (w "∂")
    t := expectOrZero t (toMultivector (∂ω)) (fld c "boundary") (w "∂ notation")
    t := expectOrZero t (toMultivector (differential ω)) (fld c "differential") (w "d")
    t := expectOrZero t (toMultivector (Calculus.d ω)) (fld c "differential") (w "d (short)")
    t := expectOrZero t (toMultivector (codifferential ω)) (fld c "codifferential") (w "δ")
    t := expectOrZero t (toMultivector (Calculus.δ ω)) (fld c "codifferential") (w "δ (short)")
    t := expectOrZero t (toMultivector (gradient ω)) (fld c "gradient") (w "gradient")
    t := expectOrZero t (toMultivector (grad ω)) (fld c "gradient") (w "grad")
    t := expectOrZero t (toMultivector (divergence ω)) (fld c "divergence") (w "divergence")
    t := expectOrZero t (toMultivector (curl ω)) (fld c "curl") (w "curl")
    -- the multivector forms agree
    t := expectOrZero t (boundaryM ω) (fld c "boundary") (w "boundaryM")
    t := expectOrZero t (differentialM ω) (fld c "differential") (w "differentialM")
    t := expectOrZero t (codifferentialM ω) (fld c "codifferential") (w "codifferentialM")
    t := expectOrZero t (curlM ω) (fld c "curl") (w "curlM")
    -- d ∘ d = 0 and ∂ ∘ ∂ = 0
    t := t.ok ((toMultivector (differential (differential ω))).v.toList.all (·.abs ≤ 1e-12)) (w "d∘d = 0")
    t := t.ok ((toMultivector (boundary (boundary ω))).v.toList.all (·.abs ≤ 1e-12)) (w "∂∘∂ = 0")
  else
    let ω : Multivector V Float := mvOf V (flts (fld c "x"))
    t := expectOrZero t (boundary ω) (fld c "boundary") (w "∂")
    t := expectOrZero t (∂ω) (fld c "boundary") (w "∂ notation")
    t := expectOrZero t (differential ω) (fld c "differential") (w "d")
    t := expectOrZero t (codifferential ω) (fld c "codifferential") (w "δ")
    t := expectOrZero t (curl ω) (fld c "curl") (w "curl")
    t := expectOrZero t (boundaryM ω) (fld c "boundary") (w "boundaryM")
    t := expectOrZero t (curlM ω) (fld c "curl") (w "curlM")
  return t

/-- The space of a `plain` case. -/
def plainCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  match (fld c "sig").getStr?.toOption.getD "" with
  | "++" => plainIn S!"++" t c k
  | "+++" => plainIn S!"+++" t c k
  | "++++" => plainIn S!"++++" t c k
  | "-+++" => plainIn S!"-+++" t c k
  | "∞∅++" => plainIn S!"∞∅++" t c k
  | s => t.ok false fun _ => s!"unknown space {s}"

/-- One simplex case: `m` points of `ℝᵂ` (homogeneous coordinates). -/
def simplexIn (mm W : Nat) (t : Tally) (c : Json) (k : Nat) : Tally :=
  let pts := (arr (fld c "points")).toList.map flts
  let T : Simplex (En mm) (En W) Float := TensorOperator.ofFn fun i j => (pts[j.1]!)[i.1]!
  let want := fld c "boundary"
  let t := t.nums m (dense (toMultivector (simplexBoundary T))) want fun _ => s!"simplex {k} m={mm} W={W}"
  t.nums m (dense (toMultivector (∂T))) want fun _ => s!"simplex {k} m={mm} W={W} (∂ notation)"

/-- The shape of a simplex case. -/
def simplexCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  match (fld c "m").getNat?.toOption.getD 0, (fld c "W").getNat?.toOption.getD 0 with
  | 2, 2 => simplexIn 2 2 t c k
  | 2, 3 => simplexIn 2 3 t c k
  | 3, 3 => simplexIn 3 3 t c k
  | 3, 4 => simplexIn 3 4 t c k
  | 4, 4 => simplexIn 4 4 t c k
  | a, b => t.ok false fun _ => s!"unknown simplex shape {a}×{b}"

/-- A chain of the non-tangent generators of `V` (the first `base`) from its coefficients. -/
def baseChain (V : TensorBundle) (base g : Nat) (xs : List Float) : Chain V g Float :=
  let blades := Leibniz.indexBasis V.n g
  let lim : UInt64 := (1 : UInt64) <<< base.toUInt64
  let (vals, _) := blades.foldl (init := (#[], xs)) fun (acc, rest) b =>
    if b < lim then (acc.push (rest.headD 0), rest.drop 1) else (acc.push 0, rest)
  chainOf V g vals.toList

/-- One `tangent` case. -/
def tangentCase (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let base := (fld c "base").getNat?.toOption.getD 0
  let mu := (fld c "mu").getNat?.toOption.getD 0
  let nu := (fld c "nu").getNat?.toOption.getD 0
  let V := (TensorBundle.euclidean base).tangent mu nu
  let what := (fld c "what").getStr?.toOption.getD ""
  let w := fun (s : String) => fun (_ : Unit) => s!"tangent case {k} tangent(ℝ^{base},{mu},{nu}) {what} {s}"
  let mut t := t
  if what == "nabla" then
    t := t.nums m (dense (nablaM V Float)) (fld c "out") (w "V(∇)")
  else
    let g := (fld c "grade").getNat?.toOption.getD 0
    let ω := baseChain V base g (flts (fld c "x"))
    t := t.nums m (dense (boundaryM ω)) (fld c "boundary") (w "∂")
    t := t.nums m (dense (differentialM ω)) (fld c "differential") (w "d")
    t := t.nums m (dense (hodge (differentialM ω))) (fld c "hodge_differential") (w "⋆d")
  return t

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "calculus"
  let t := (arr (fld j "plain")).toList.zipIdx.foldl (fun t (c, k) => plainCase t c k) (Tally.new "forms/calculus")
  let t := (arr (fld j "simplices")).toList.zipIdx.foldl (fun t (c, k) => simplexCase t c k) t
  let t := (arr (fld j "tangent")).toList.zipIdx.foldl (fun t (c, k) => tangentCase t c k) t
  -- the static result types
  let v : Chain S!"+++" 1 Float := chainOf _ 1 [1, 2, 3]
  let _ : Chain S!"+++" 0 Float := boundary v
  let _ : Chain S!"+++" 2 Float := differential v
  let _ : Chain S!"+++" 1 Float := curl v
  let t := t.ok ((boundary v).v.toList == [6]) fun _ => s!"∂(v1+2v2+3v3) = {(boundary v).v.toList}"
  -- simplicial complexes (docs `39-simplicial`, Julia's values)
  let R5 := En 5
  let blade := fun (b : UInt64) => (termMV R5 b 1 : Multivector R5 Float)
  let ω := blade 7
  let sk := skeleton ω
  let want : List (UInt64 × Float) := [(1, 2), (2, 2), (4, 2), (3, 1), (5, 1), (6, 1), (7, 1)]
  let t := t.ok ((Leibniz.indexBasisAll 5).toList.zip sk.v.toList |>.all fun (b, x) =>
      x == ((want.find? (·.1 == b)).map (·.2)).getD 0) fun _ => s!"skeleton(v123) = {sk.v.toList}"
  let t := t.ok (χ sk == 1 && betti sk == #[1, 0, 0, 0, 0]) fun _ => s!"χ, betti of skeleton(v123): {χ sk} {betti sk}"
  let t := t.ok (χ (skeleton (boundaryM ω)) == 0 && betti (skeleton (boundaryM ω)) == #[1, 1, 0, 0, 0]) fun _ =>
    "χ, betti of skeleton(∂v123)"
  let ws : List UInt64 := [3, 7, 15, 31]
  let t := t.ok (ws.map (fun b => (χ (skeleton (blade b)), χ (skeleton (boundaryM (blade b))))) == [(1, 2), (1, 0), (1, 2), (1, 0)])
    fun _ => "χ pairs"
  let t := t.ok (ws.map (fun b => betti (skeleton (boundaryM (blade b)))) ==
      [#[2, 0, 0, 0, 0], #[1, 1, 0, 0, 0], #[0, -2, 0, 0, 0], #[1, -4, -5, 0, 0]]) fun _ =>
    s!"betti list {ws.map (fun b => betti (skeleton (boundaryM (blade b))))}"
  let v1234 : Single R5 4 Float := ⟨15, 1⟩
  let t := t.ok ((chain v1234).v.toList == [1, 0, -1, 0, 1, 0, 0, 1, 0, 0] &&
      (path v1234).v.toList == [1, 0, 0, 0, 1, 0, 0, 1, 0, 0]) fun _ => s!"chain, path of v1234: {(chain v1234).v.toList}"
  -- 𝒫 keeps the empty face; subcomplex is the skeleton of the boundary; count_gdims, boundary_null
  let t := t.ok (getD (𝒫 ω).v 0 == 6 && (subcomplex ω).v.toList == (skeleton (absym (boundaryM ω))).v.toList) fun _ =>
    s!"𝒫, subcomplex: {(𝒫 ω).v.toList}"
  let t := t.ok (countGdims sk == #[0, 3, 3, 1, 0, 0] && boundaryNull sk == #[3, 1, 0, 0, 0, 0]) fun _ =>
    s!"count_gdims, boundary_null: {countGdims sk} {boundaryNull sk}"
  return t

end Tests.FormsTests.CalculusSuite
