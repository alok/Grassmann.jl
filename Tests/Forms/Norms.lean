import Tests.Forms.Common

/-!
# `abs`, `unit`, `unitize`, `unitnorm`, `geomabs` per element kind against Julia

Golden `oracle/golden/forms/norms.json` (`oracle/forms/gen_parity.jl`): random chains of grade
1 and 2, terms and couples on `v₁₂`, spinors and co-spinors of `S"+++"`, `S"-+++"`,
`S"++++"`, `S"++-"`; each function's Julia result kind and dense coefficients. The
static result kinds are those of `Grassmann.Composite.Norm` (a scalar `Single` for `abs`
of chains, terms and couples, a `Couple` for their `geomabs`); values `rtol = 1e-13`.
Julia errors (`DomainError` of `sqrt` of a negative scalar, `inv` undefined in the spinor
square root) are skipped.
-/

namespace Tests.FormsTests.Norms

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests JuliaBase

/-- Dense coefficients as scalars. -/
def dense {V : TensorBundle} (m : Multivector V Float) : List Num := m.v.toList.map .flt

/-- Compare a result's dense vector (and Julia's kind name) with the golden entry. -/
def cmp {V : TensorBundle} (t : Tally) (kind : String) (m : Multivector V Float) (want : Json)
    (what : Unit → String) : Tally :=
  if (jerr? want).isSome then t.skip
  else
    let t := t.ok ((fld want "kind").getStr?.toOption == some kind)
      fun _ => s!"{what ()}: kind {kind} vs Julia {(fld want "kind").compress}"
    t.nums (.approx 1e-13) (dense m) (fld want "dense") what

/-- One case in the space `V`. -/
def caseIn (V : TensorBundle) [Kernels V] (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let m : Multivector V Float := mvOf V (flts (fld c "in"))
  let kind := (fld c "kind").getStr?.toOption.getD ""
  let w := fun (s : String) => fun (_ : Unit) => s!"norms case {k} {V} {kind} {s}"
  let mut t := t
  match kind with
  | "chain1" =>
    let x : Chain V 1 Float := gradePart m 1
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "Chain" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "Chain" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "Chain" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" (toMultivector x.geomabs) (fld c "geomabs") (w "geomabs")
  | "chain2" =>
    let x : Chain V 2 Float := gradePart m 2
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "Chain" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "Chain" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "Chain" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" (toMultivector x.geomabs) (fld c "geomabs") (w "geomabs")
  | "single" =>
    let x : Single V 2 Float := ⟨3, m.coeff 3⟩
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "Single" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "Single" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "Single" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" (toMultivector x.geomabs) (fld c "geomabs") (w "geomabs")
  | "couple" =>
    let x : Couple V Float := ⟨3, m.coeff 0, m.coeff 3⟩
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "Couple" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "Couple" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "Couple" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" (toMultivector x.geomabs) (fld c "geomabs") (w "geomabs")
  | "spinor" =>
    let x : Half V false Float := toHalf m false
    -- Julia's `abs` of a spinor is a scalar `Single` where it is defined (spaces of
    -- dimension ≤ 3 here); the typed result is the scalar spinor
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "Spinor" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "Spinor" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "Spinor" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" x.geomabs (fld c "geomabs") (w "geomabs")
  | _ =>
    let x : Half V true Float := toHalf m true
    t := cmp t "Single" (toMultivector x.abs) (fld c "abs") (w "abs")
    t := cmp t "CoSpinor" (toMultivector x.unit) (fld c "unit") (w "unit")
    t := cmp t "CoSpinor" (toMultivector x.unitize) (fld c "unitize") (w "unitize")
    t := cmp t "CoSpinor" (toMultivector x.unitnorm) (fld c "unitnorm") (w "unitnorm")
    t := cmp t "Couple" x.geomabs (fld c "geomabs") (w "geomabs")
  return t

/-- The space of a case. -/
def dispatch (t : Tally) (c : Json) (k : Nat) : Tally :=
  match (fld c "sig").getStr?.toOption.getD "" with
  | "+++" => caseIn S!"+++" t c k
  | "-+++" => caseIn S!"-+++" t c k
  | "++++" => caseIn S!"++++" t c k
  | "++-" => caseIn S!"++-" t c k
  | s => t.ok false fun _ => s!"unknown space {s}"

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "norms"
  return (cases j).toList.zipIdx.foldl (fun t (c, k) => dispatch t c k) (Tally.new "forms/norms")

end Tests.FormsTests.Norms
