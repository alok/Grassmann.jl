import Tests.Forms.Common

/-!
# `exp`, `expm1`, `log` of outermorphisms, dyadics and projectors against Julia

Golden `oracle/golden/forms/opfun.json` (`oracle/forms/gen_opfun.jl`):

* `outermorphism`: `exp`, `expm1` of the outermorphism of `A + 2I` (`n = 2 … 4`) as its
  compounds (`rtol = 1e-12`); Julia's `log(::Outermorphism)` throws a `MethodError` (the
  `Endomorphism{V}(log(Matrix))` it builds does not convert), so `Outermorphism.log` is checked
  against Julia's grade-1 `log(A)` (`rtol = 1e-9`: Julia's Schur logarithm, the eigenvector
  formula here); its higher blocks are the compounds of that map by construction.
* `dyadic`: `exp`, `expm1` of `x ⊗ y` (`rtol = 1e-12`).
* `projector`: `Proj(v, λ)` (the normalised vector), `exp(P)` (Julia's first-column heuristic).

The logarithms of rank-one maps (`Dyadic.log`, `Projector.log`) are not compared: the maps are
singular for `n ≥ 2`, so both sides' values come from the rounding of the zero eigenvalues
(`log(1e-15)`-sized entries, or a complex result on one side only).
-/

namespace Tests.FormsTests.OpFunSuite

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- The rows of a golden matrix as floats. -/
def rowsOf (j : Json) : List (List Float) := floatRows j

/-- One outermorphism case in `ℝⁿ`. -/
def outerIn (n : Nat) (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let A : Endomorphism (En n) (.chain 1) Float := endo (En n) (rowsOf (fld c "A"))
  let O := A.outermorphism
  let w := fun (s : String) => fun (_ : Unit) => s!"outermorphism case {k} n={n} {s}"
  let mut t := t
  let blocksOf := fun (P : Outermorphism (En n) (En n) Float) =>
    (List.range n).map fun g => opRows (P.block (g + 1))
  let cmpBlocks := fun (t : Tally) (P : Outermorphism (En n) (En n) Float) (want : Json) (s : String) =>
    if (jerr? want).isSome then t.skip
    else
      let ws := arr want
      (blocksOf P).zipIdx.foldl (fun t (b, g) => t.mat (.approx 1e-12) b (ws[g]?.getD .null) (w s!"{s} block {g + 1}")) t
  t := cmpBlocks t O.exp (fld c "exp") "exp"
  t := cmpBlocks t O.expm1 (fld c "expm1") "expm1"
  match O.log with
  | .ok L =>
    t := t.mat (.approx 1e-9) (opRows L.base) (fld c "log_base") (w "log (grade 1)")
  | .error e => t := t.ok false (w s!"log: {e}")
  return t

/-- One dyadic case in `ℝⁿ`. -/
def dyadicIn (n : Nat) (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let D : Dyadic (En n) 1 (En n) 1 Float := ⟨chainOf (En n) 1 (flts (fld c "x")), chainOf (En n) 1 (flts (fld c "y"))⟩
  let w := fun (s : String) => fun (_ : Unit) => s!"dyadic case {k} n={n} {s}"
  let mut t := t
  t := t.mat (.approx 1e-12) (opRows D.exp) (fld c "exp") (w "exp")
  t := t.mat (.approx 1e-12) (opRows D.expm1) (fld c "expm1") (w "expm1")
  return t

/-- One projector case in `ℝⁿ`. -/
def projIn (n : Nat) (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let lam := (flts (.arr #[fld c "lambda"])).headD 0
  let P : Projector (En n) 1 Float := Projector.ofVector (chainOf (En n) 1 (flts (fld c "v"))) lam
  let w := fun (s : String) => fun (_ : Unit) => s!"projector case {k} n={n} {s}"
  let mut t := t
  t := t.nums (.approx 1e-14) (P.v.v.toList.map .flt) (fld (fld c "P") "v") (w "Proj(v, λ).v")
  let e := fld c "exp"
  if (jerr? e).isNone then
    let Pe := P.exp
    t := t.nums (.approx 1e-12) (Pe.v.v.toList.map .flt) (fld e "v") (w "exp(P).v")
    t := t.nums (.approx 1e-12) [.flt Pe.lam] (.arr #[fld e "lambda"]) (w "exp(P).λ")
  return t

/-- The dimension of a case. -/
def byDim (f : (n : Nat) → Tally → Json → Nat → Tally) (t : Tally) (c : Json) (k : Nat) : Tally :=
  match (fld c "n").getNat?.toOption.getD 0 with
  | 2 => f 2 t c k
  | 3 => f 3 t c k
  | 4 => f 4 t c k
  | m => t.ok false fun _ => s!"unexpected dimension {m}"

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "opfun"
  let t := (arr (fld j "outermorphism")).toList.zipIdx.foldl (fun t (c, k) => byDim outerIn t c k) (Tally.new "forms/opfun")
  let t := (arr (fld j "dyadic")).toList.zipIdx.foldl (fun t (c, k) => byDim dyadicIn t c k) t
  let t := (arr (fld j "projector")).toList.zipIdx.foldl (fun t (c, k) => byDim projIn t c k) t
  return t

end Tests.FormsTests.OpFunSuite
