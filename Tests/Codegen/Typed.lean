/-
The generated kernels behind the typed operations, at `Float` (the specialized
path): for each standard space the typed products, sandwiches and maps at
concrete element types (whose dispatch folds to specialized kernels, as in
user code) equal the reference kernels on random operands, bit for bit up to
the sign of zero.

Also `basis!`'s kernel emission: a non-standard space gets kernels (and the
typed operations agree with the reference there too), and
`basis! (kernels := false)` emits none.
-/
import Tests.Codegen.Diag

open Grassmann DirectSum StaticVectors Grassmann.Kernel

namespace CodegenTests.Typed

/-- Exact equality of two packed vectors (as arrays). -/
@[inline] def same {n m : Nat} (x : Values Float n) (y : Values Float m) : Bool := x.toArray == y.toArray

/-- The typed operations of `V` at `Float` against the reference kernels. Specialized on the
`Kernels V` instance at each call site, so the typed operations run the generated kernels
(or the fallback, for spaces without them) exactly as user code does. -/
@[specialize] def checkTyped (name : String) (V : TensorBundle) [Kernels V] (seed : Nat) (t : Tally) :
    Tally := Id.run do
  let n := V.n
  let mut t := t
  let mut rng := Tests.Rng.ofSeed seed
  for _ in [0:20] do
    let ((a, b, s, r, u, w, c2), g) := (do
        return (← randFloat (2 ^ n), ← randFloat (2 ^ n), ← randFloat ((Layout.even).size n),
          ← randFloat ((Layout.even).size n), ← randFloat (Layout.size n (.chain 1)),
          ← randFloat (Layout.size n (.chain 1)), ← randFloat (Layout.size n (.chain 2))) :
        Tests.Gen _) |> (StateT.run · rng)
    rng := g
    let A : Multivector V Float := ⟨a⟩
    let B : Multivector V Float := ⟨b⟩
    let S : Spinor V Float := ⟨s⟩
    let R : Spinor V Float := ⟨r⟩
    let U : Chain V 1 Float := ⟨u⟩
    let W : Chain V 1 Float := ⟨w⟩
    let C : Chain V 2 Float := ⟨c2⟩
    t := t.check (same (A * B).v (refBin V .mul .full .full .full a b)) s!"{name} Multivector*Multivector"
    t := t.check (same (S * R : Spinor V Float).v (refBin V .mul .even .even .even s r)) s!"{name} Spinor*Spinor"
    t := t.check (same (U ∧ W : Chain V 2 Float).v (refBin V .wedge (.chain 1) (.chain 1) (.chain 2) u w))
      s!"{name} Chain1∧Chain1"
    t := t.check (same (C * U : CoSpinor V Float).v (refBin V .mul (.chain 2) (.chain 1) .odd c2 u))
      s!"{name} Chain2*Chain1"
    t := t.check (same (U ⋅ W : Chain V 0 Float).v (refBin V .contraction (.chain 1) (.chain 1) (.chain 0) u w))
      s!"{name} Chain1⋅Chain1"
    -- sandwiches: `v ⊘ R = (~R) v R` and `R >>> v = R v clifford(R)`, projected onto grade 1
    let sw := refBinProj V .mul .odd .even (.chain 1) (refBin V .reverseMul .even (.chain 1) .odd r u) r
    t := t.check (same (U ⊘ R : Chain V 1 Float).v sw) s!"{name} Chain1 ⊘ Spinor"
    let ts := refBinProj V .mul .odd .even (.chain 1) (refBin V .mul .even (.chain 1) .odd r u)
      (refUn V .clifford .even .even r)
    t := t.check (same (R >>> U : Chain V 1 Float).v ts) s!"{name} Spinor >>> Chain1"
    -- `R * v * ~R` through the typed products
    let rv := refBin V .mul .odd .even .odd (refBin V .mul .even (.chain 1) .odd r u) (refUn V .reverse .even .even r)
    t := t.check (same (R * U * ~R : CoSpinor V Float).v rv) s!"{name} R*v*~R"
    t := t.check (same (~A).v (refUn V .reverse .full .full a)) s!"{name} reverse"
    t := t.check (same (⋆A : Multivector V Float).v (refUn V .complementrighthodge .full .full a)) s!"{name} hodge"
    t := t.check (same (⋆U : Chain V (n - 1) Float).v (refUn V .complementrighthodge (.chain 1) (.chain (n - 1)) u))
      s!"{name} hodge Chain1"
  return t

end CodegenTests.Typed

/-! ## `basis!` emission -/

namespace CodegenTests.BasisHook
basis! S!"++-"
end CodegenTests.BasisHook

namespace CodegenTests.BasisOff
basis! (kernels := false) S!"+--+"
end CodegenTests.BasisOff

namespace CodegenTests.Options
-- a policy override: no dense families, and no kernel above 8 entries
grassmann_kernels (dense := false) (maxEntries := 8) S!"-+-"
end CodegenTests.Options

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.contains `CodegenTests.BasisHook.kernels.instKernels do
    throwError "basis! S!\"++-\" did not emit kernels"
  if (Grassmann.Kernel.Codegen.registered? env S!"+--+").isSome || env.contains `CodegenTests.BasisOff.kernels.space then
    throwError "basis! (kernels := false) emitted kernels"
  unless (Grassmann.Kernel.Codegen.registered? env ℝ3) == some `Grassmann.Kernel.Gen.ℝ3 do
    throwError "ℝ3 is not registered with its pre-generated kernels"
  let pre := Name.mkSimple (toString S!"-+-")
  let opt := `CodegenTests.Options ++ pre
  unless (Grassmann.Kernel.Codegen.registered? env S!"-+-") == some opt do
    throwError "grassmann_kernels (options) S!\"-+-\" is not registered under {opt}"
  -- `(maxEntries := 8)` drops the 64-entry multivector product, `(dense := false)` the dense
  -- families; the 6-entry vector wedge and the 8-entry reverse stay
  if env.contains (opt ++ `k_bin_mul_f_f_f) || env.contains (opt ++ `k_bin_wedge_f_c1_f) then
    throwError "grassmann_kernels (options) emitted a dense or oversized kernel"
  unless env.contains (opt ++ `k_bin_wedge_c1_c1_c2) && env.contains (opt ++ `k_un_reverse_f_f) do
    throwError "grassmann_kernels (options) omitted a small kernel"

namespace CodegenTests.Typed

/-- Run the suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  t := checkTyped "ℝ2" ℝ2 11 t
  t := checkTyped "ℝ3" ℝ3 12 t
  t := checkTyped "ℝ4" ℝ4 13 t
  t := checkTyped "STA" STA 14 t
  t := checkTyped "PGA2" PGA2 15 t
  t := checkTyped "PGA3" PGA3 16 t
  t := checkTyped "CGA2" CGA2 17 t
  t := checkTyped "CGA3" CGA3 18 t
  t := checkTyped "basis! ⟨++-⟩" CodegenTests.BasisHook.V 19 t
  t := checkTyped "reference ⟨+--+⟩" CodegenTests.BasisOff.V 20 t
  t := checkTyped "grassmann_kernels (options) ⟨-+-⟩" S!"-+-" 21 t
  t := checkTyped "grassmann_kernels ⟨1,2,-3⟩" D!"1,2,-3" 22 t
  return t

end CodegenTests.Typed
