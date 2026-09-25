/-
Shared pieces of the fusion tests (`Grassmann.Fuse`): random operands of the typed containers,
the comparison of a fused result with the unfused one, and `fcheck`, which states one check
from one expression.
-/
import Grassmann
import Grassmann.Fuse
import Tests.Codegen.Common

open Grassmann DirectSum StaticVectors

namespace FuseTests

export GrassmannTests (Tally)

/-- Random operands of a typed container (or a coefficient). -/
class Rand (X : Type) where
  /-- A random element. -/
  gen : Tests.Gen X

instance {V : TensorBundle} {G : Nat} : Rand (Chain V G Float) := ⟨return ⟨← CodegenTests.randFloat _⟩⟩
instance {V : TensorBundle} {p : Bool} : Rand (Half V p Float) := ⟨return ⟨← CodegenTests.randFloat _⟩⟩
instance {V : TensorBundle} : Rand (Multivector V Float) := ⟨return ⟨← CodegenTests.randFloat _⟩⟩
instance {V : TensorBundle} {G : Nat} : Rand (Chain V G Int) := ⟨return ⟨← CodegenTests.randInt _⟩⟩
instance {V : TensorBundle} {p : Bool} : Rand (Half V p Int) := ⟨return ⟨← CodegenTests.randInt _⟩⟩
instance {V : TensorBundle} : Rand (Multivector V Int) := ⟨return ⟨← CodegenTests.randInt _⟩⟩
instance : Rand Float := ⟨Tests.Gen.floatIn (-2) 2⟩
instance : Rand Int := ⟨Tests.Gen.int (-4) 4⟩

/-- Equality of results: coefficientwise `==` (so `-0 == 0` and a fused result equals the unfused
one "up to the sign of zero"). -/
class Same (X : Type) where
  /-- The results agree. -/
  same : X → X → Bool

instance {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] [BEq α] : Same (Chain V G α) :=
  ⟨fun a b => a.v.toArray == b.v.toArray⟩
instance {V : TensorBundle} {p : Bool} {α : Type} [Coeff α] [BEq α] : Same (Half V p α) :=
  ⟨fun a b => a.v.toArray == b.v.toArray⟩
instance {V : TensorBundle} {α : Type} [Coeff α] [BEq α] : Same (Multivector V α) :=
  ⟨fun a b => a.v.toArray == b.v.toArray⟩
instance : Same Float := ⟨(· == ·)⟩
instance : Same Int := ⟨(· == ·)⟩

/-- Number of random trials per check. -/
def trials : Nat := 25

/-- Compare `f` (unfused) with `g` (fused) on random operands. -/
def check1 {X R : Type} [Rand X] [Same R] (name : String) (f g : X → R) (seed : Nat) (t : Tally) : Tally :=
  Id.run do
    let mut rng := Tests.Rng.ofSeed seed
    let mut ok := true
    for _ in [0:trials] do
      let (x, r) := StateT.run (Rand.gen : Tests.Gen X) rng
      rng := r
      ok := ok && Same.same (f x) (g x)
    return t.check ok s!"{name}: fused ≠ unfused"

/-- Compare two-operand expressions. -/
def check2 {X Y R : Type} [Rand X] [Rand Y] [Same R] (name : String) (f g : X → Y → R) (seed : Nat)
    (t : Tally) : Tally :=
  Id.run do
    let mut rng := Tests.Rng.ofSeed seed
    let mut ok := true
    for _ in [0:trials] do
      let ((x, y), r) := StateT.run (do return (← (Rand.gen : Tests.Gen X), ← (Rand.gen : Tests.Gen Y)) : Tests.Gen _) rng
      rng := r
      ok := ok && Same.same (f x y) (g x y)
    return t.check ok s!"{name}: fused ≠ unfused"

/-- Compare three-operand expressions. -/
def check3 {X Y Z R : Type} [Rand X] [Rand Y] [Rand Z] [Same R] (name : String) (f g : X → Y → Z → R)
    (seed : Nat) (t : Tally) : Tally :=
  Id.run do
    let mut rng := Tests.Rng.ofSeed seed
    let mut ok := true
    for _ in [0:trials] do
      let ((x, y, z), r) := StateT.run (do
        return (← (Rand.gen : Tests.Gen X), ← (Rand.gen : Tests.Gen Y), ← (Rand.gen : Tests.Gen Z)) :
          Tests.Gen _) rng
      rng := r
      ok := ok && Same.same (f x y z) (g x y z)
    return t.check ok s!"{name}: fused ≠ unfused"

/-- `fcheck "name" (x : X) => e`: check `fused% e` against `e` (one to three operands). -/
syntax "fcheck " term:max ("(" ident " : " term ")")+ " => " term : term

macro_rules
  | `(fcheck $nm ($a : $ta) => $e) => `(check1 $nm (fun ($a : $ta) => $e) (fun ($a : $ta) => fused% $e))
  | `(fcheck $nm ($a : $ta) ($b : $tb) => $e) =>
    `(check2 $nm (fun ($a : $ta) ($b : $tb) => $e) (fun ($a : $ta) ($b : $tb) => fused% $e))
  | `(fcheck $nm ($a : $ta) ($b : $tb) ($c : $tc) => $e) =>
    `(check3 $nm (fun ($a : $ta) ($b : $tb) ($c : $tc) => $e) (fun ($a : $ta) ($b : $tb) ($c : $tc) => fused% $e))

end FuseTests
