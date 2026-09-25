import Bench.Grassmann.Products
import Grassmann.Batch

/-!
# Batch kernels against Julia's `map` over `Vector`s of elements

`grassmann/<space>/batch <op>`: one body call applies the operation to the `K = 1024` element
pairs of two batches (`Grassmann.Batch`, element-major `FloatArray`s: the layout of Julia's
`Vector{Chain}`), pairing element `i` with element `i`, and returns the sum of the first and the
last result's coefficients (`Batch.check`): `K` operations per call. The Julia twin times
`map(f, xs, ys)` (a fresh result vector per call, like `batch%`) and, for the `(into)` cases,
`map!(f, out, xs, ys)` into a preallocated vector (like `batchInto%` writing into an exclusive
output batch). The operands are the rings of the product cases (same seeds).
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum StaticVectors Bench

/-- A batch case writing into a reused output batch (`batchInto%`): the output is taken out of
its reference before the call, so it is exclusive and written in place. -/
@[inline] def intoCase {X Y Z : Type} (name : String) (xs : Batch X) (ys : Batch Y) (out0 : Batch Z)
    (k : Batch Z → Batch X → Batch Y → Batch Z) [BatchElem Z] : BenchM Unit := do
  let r ← IO.mkRef out0
  benchIO name (ops := ringSize) (param := s!"K={ringSize}") fun s => do
    let o ← r.swap default
    let o := k o (blackBox s xs) ys
    let c := Batch.check o
    r.set o
    return c

/-! ## The layout experiment: component-major batches

`batchSoA% f` is `batch% f` reading and writing component-major arrays (coefficient `j` of
element `i` at `j·n + i`, `Grassmann.Fuse.batchKernel (soa := true)`), for the `[soa]` cases
that compare the two layouts on the same operations. -/

/-- `batch%` on component-major arrays (layout experiment only; see above). -/
syntax (name := batchSoAStx) "batchSoA% " term : term

open Lean Elab in
/-- Elaborate `batchSoA% f` (component-major `batch%`). -/
@[term_elab batchSoAStx] def elabBatchSoA : Term.TermElab := fun stx _ => match stx with
  | `(batchSoA% $t) => do
    let f ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    Grassmann.Fuse.batchKernel (← instantiateMVars f) false (soa := true)
  | _ => throwUnsupportedSyntax

/-- A batch in component-major order (its `data` transposed). -/
def toSoA {X : Type} [BatchElem X] (b : Batch X) : Batch X :=
  let k := BatchElem.width X
  ⟨b.len, (Array.range (b.len * k)).foldl (init := FloatArray.emptyWithCapacity (b.len * k))
    fun acc t => acc.push (b.data.get! ((t % b.len) * k + t / b.len))⟩

/-- `Batch.check` of a component-major batch. -/
def soaCheck {X : Type} [BatchElem X] (b : Batch X) : Float :=
  let k := BatchElem.width X
  let n := b.len
  (List.range k).foldl (fun acc j => acc + b.data.get! (j * n)) 0 +
    (List.range k).foldl (fun acc j => acc + b.data.get! (j * n + n - 1)) 0

/-- `batch_cases% "label" V seed`: the batch cases of one space (rings seeded as `space_cases%`). -/
syntax (name := batchCasesStx) "batch_cases% " str term:max num : term

macro_rules
  | `(batch_cases% $label $V $seed) => `(show Bench.BenchM Unit from do
      let n := ($V).n
      let p := s!"K={ringSize}"
      let k (s : String) := $label ++ "/batch " ++ s
      let M := Batch.ofArray (ringOf (2 ^ n) ($seed * 16 + 1) (Multivector.mk (V := $V) (α := Float)))
      let N := Batch.ofArray (ringOf (2 ^ n) ($seed * 16 + 2) (Multivector.mk (V := $V) (α := Float)))
      let S := Batch.ofArray (ringOf (halfDim n false) ($seed * 16 + 3) (Half.mk (V := $V) (odd := false) (α := Float)))
      let T := Batch.ofArray (ringOf (halfDim n false) ($seed * 16 + 4) (Half.mk (V := $V) (odd := false) (α := Float)))
      let U := Batch.ofArray (ringOf (Leibniz.binomial n 1) ($seed * 16 + 5) (Chain.mk (V := $V) (G := 1) (α := Float)))
      let W := Batch.ofArray (ringOf (Leibniz.binomial n 1) ($seed * 16 + 6) (Chain.mk (V := $V) (G := 1) (α := Float)))
      bench (k "Spinor*Spinor") (ops := ringSize) (param := p) fun s =>
        Batch.check ((batch% fun (x y : Spinor $V Float) => (x * y : Spinor $V Float)) (blackBox s S) T)
      bench (k "Chain1∧Chain1") (ops := ringSize) (param := p) fun s =>
        Batch.check ((batch% fun (a b : Chain $V 1 Float) => (a ∧ b : Chain $V 2 Float)) (blackBox s U) W)
      bench (k "R*v*~R") (ops := ringSize) (param := p) fun s =>
        Batch.check ((batch% fun (R : Spinor $V Float) (v : Chain $V 1 Float) =>
          (R * v * ~R : CoSpinor $V Float)) (blackBox s S) U)
      bench (k "v ⊘ R") (ops := ringSize) (param := p) fun s =>
        Batch.check ((batch% fun (R : Spinor $V Float) (v : Chain $V 1 Float) =>
          (v ⊘ R : Chain $V 1 Float)) (blackBox s S) U)
      bench (k "Multivector*Multivector") (ops := ringSize) (param := p) fun s =>
        Batch.check ((batch% fun (a b : Multivector $V Float) => a * b) (blackBox s M) N)
      intoCase (k "Spinor*Spinor (into)") S T (Batch.zeros (X := Half $V false Float) ringSize)
        (batchInto% fun (x y : Spinor $V Float) => (x * y : Spinor $V Float))
      intoCase (k "R*v*~R (into)") S U (Batch.zeros (X := Half $V true Float) ringSize)
        (batchInto% fun (R : Spinor $V Float) (v : Chain $V 1 Float) => (R * v * ~R : CoSpinor $V Float))
      -- the same operations on component-major arrays (layout experiment)
      let (S', T', U', M', N') := (toSoA S, toSoA T, toSoA U, toSoA M, toSoA N)
      bench (k "Spinor*Spinor [soa]") (ops := ringSize) (param := p) fun s =>
        soaCheck ((batchSoA% fun (x y : Spinor $V Float) => (x * y : Spinor $V Float)) (blackBox s S') T')
      bench (k "R*v*~R [soa]") (ops := ringSize) (param := p) fun s =>
        soaCheck ((batchSoA% fun (R : Spinor $V Float) (v : Chain $V 1 Float) =>
          (R * v * ~R : CoSpinor $V Float)) (blackBox s S') U')
      bench (k "Multivector*Multivector [soa]") (ops := ringSize) (param := p) fun s =>
        soaCheck ((batchSoA% fun (a b : Multivector $V Float) => a * b) (blackBox s M') N'))

end Bench.Grassmann

namespace Bench.Grassmann

open _root_.Grassmann DirectSum Bench

set_option maxHeartbeats 1000000 in
/-- Batch cases of `ℝ3`. -/ def batchR3 : BenchM Unit := batch_cases% "ℝ3" ℝ3 2
set_option maxHeartbeats 1000000 in
/-- Batch cases of `STA`. -/ def batchSTA : BenchM Unit := batch_cases% "STA" STA 4
set_option maxHeartbeats 1000000 in
/-- Batch cases of `PGA3`. -/ def batchPGA3 : BenchM Unit := batch_cases% "PGA3" PGA3 6
set_option maxHeartbeats 1000000 in
/-- Batch cases of `CGA3`. -/ def batchCGA3 : BenchM Unit := batch_cases% "CGA3" CGA3 8

end Bench.Grassmann
