import AbstractAnalysis
import Tests.AbstractAnalysis.Harness

/-!
Oracle tests for the countable sets (`oracle/golden/abstractanalysis/sets.json`)
plus properties of the clean pairings.
-/

open Lean AbstractAnalysis JuliaBase Tests.Golden

namespace Tests.AbstractAnalysis.Sets

/-- Compare a whole sequence against a golden list. -/
def seqCheck {α : Type} [BEq α] [ToString α] [Inhabited α] (name : String) (got : Nat → α) (exp : Array α) :
    TestM Unit := do
  let bad := (List.range exp.size).filter fun i => !(got (i + 1) == exp[i]!)
  match bad.head? with
  | none => check name true
  | some i => check name false s!"first mismatch at {i + 1}: got {got (i + 1)}, expected {exp[i]!}"

/-- Julia `Complex{Int}` as `[re, im]`. -/
def jComplexInt (j : Json) : Complex Int := let a := jArr j; ⟨jInt a[0]!, jInt a[1]!⟩

instance : ToString (Complex Int) := ⟨JuliaRepr.repr⟩
instance : ToString (Complex Rat) := ⟨JuliaRepr.repr⟩

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/abstractanalysis/sets.json"
  seqCheck "Integers" integer (jInts (jGet j "integers"))
  seqCheck "PositiveRationals" positiveRational ((jArr (jGet j "positiverationals")).map jRat)
  seqCheck "Rationals" rational ((jArr (jGet j "rationals")).map jRat)
  seqCheck "NonzeroRationals" nonzeroRational ((jArr (jGet j "nonzerorationals")).map jRat)
  seqCheck "CantorPairs (Julia bug)" Julia.cantorInversion
    ((jArr (jGet j "cantorpairs")).map fun p => let a := jInts p; (a[0]!, a[1]!))
  seqCheck "ElegantPairs0" (fun n => let (a, b) := elegantUnpair n; ((a : Int), (b : Int)))
    ((jArr (jGet j "elegantpairs0")).map fun p => let a := jInts p; (a[0]!, a[1]!))
  seqCheck "ElegantPairs1" (fun n => let (a, b) := elegantUnpairFrom 1 n; ((a : Int), (b : Int)))
    ((jArr (jGet j "elegantpairs1")).map fun p => let a := jInts p; (a[0]!, a[1]!))
  seqCheck "GaussianNaturals" (GaussianNaturals 1000).f ((jArr (jGet j "gaussiannaturals")).map jComplexInt)
  seqCheck "GaussianIntegers" GaussianIntegers.f ((jArr (jGet j "gaussianintegers")).map jComplexInt)
  seqCheck "GaussianRationals" GaussianRationals.f
    ((jArr (jGet j "gaussianrationals")).map fun p => let a := jArr p; (⟨jRat a[0]!, jRat a[1]!⟩ : Complex Rat))
  seqCheck "sternbrocot (fusc)" (fun n => (fusc n : Int)) (jInts (jGet j "sternbrocot"))
  let sb := (SternBrocot.take 1000).map fun (n : Nat) => (n : Int)
  seqCheck "SternBrocot memo" (fun n => sb[n - 1]!) (jInts (jGet j "SternBrocot"))
  -- clean API: Cantor pairing is a bijection on the first 10⁴ naturals
  check "cantorUnpair ∘ cantorPair" ((List.range 10000).all fun n =>
    let (x, y) := cantorUnpair n; cantorPair x y == n)
  check "elegant bijection sample" ((List.range 10000).all fun n =>
    let (a, b) := elegantUnpair n; elegantPair a b == n && elegantUnpair (elegantPair a b) == (a, b))
  -- primes (Julia's PrimesExt weak dependency is not installed: known values)
  checkEq "first primes" ((PrimeIntegers 25).toArray).toList
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
  checkEq "prime(1000)" (prime 1000) 7919
  -- positive rationals come out in lowest terms (fusc_coprime)
  check "PositiveRationals reduced" ((List.range 2000).all fun n =>
    (positiveRational (n + 1)).num.natAbs == fusc (n + 1))

end Tests.AbstractAnalysis.Sets
