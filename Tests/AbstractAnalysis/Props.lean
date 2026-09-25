import AbstractAnalysis
import Tests.AbstractAnalysis.Harness
import Tests.Util.Random

/-!
Property tests (SplitMix64) and compile-time `decide` checks for the
AbstractAnalysis port.
-/

open AbstractAnalysis Tests.Golden

namespace Tests.AbstractAnalysis.Props

/-! ## Compile-time checks (the kernel evaluates these) -/

example : (List.range 16).map (fun n => fusc (n + 1)) = [1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 5, 2, 5, 3, 4, 1] := by decide
example : fusc 100 = 7 ∧ fusc 1000 = 11 := by decide
example : (List.range 7).map (fun n => integer (n + 1)) = [0, 1, -1, 2, -2, 3, -3] := by decide
example : elegantPair 3 5 = 28 ∧ elegantPair 5 3 = 33 := by decide
example : (Perm.ofList! [2, 3, 1] : Perm 3) * Perm.ofList! [2, 1, 3] = Perm.ofList! [3, 2, 1] := by decide
example : (Perm.ofList! [2, 3, 1] : Perm 3).transpositionCount = 2 ∧ (Perm.ofList! [2, 3, 1] : Perm 3).groupOrder = 3 := by
  decide
example : (Perm.ofList? [1, 1, 2] : Option (Perm 3)) = none := by decide
example : (SymmetricGroup 4).v.size = 24 := by decide +kernel

/-! ## Randomised properties -/

/-- Random finite `Float64` from raw bits. -/
def randFinite (g : Tests.Rng) : Float × Tests.Rng :=
  let (u, g) := g.next
  let x := Float.ofBits u
  (if x.isFinite then x else Float.ofBits (u &&& 0x3FFFFFFFFFFFFFFF), g)

/-- Fisher–Yates shuffle of `1..n` as a permutation. -/
def randPerm (N : Nat) (g : Tests.Rng) : Perm N × Tests.Rng := Id.run do
  let mut a := (List.range N).toArray.map (· + 1)
  let mut g := g
  for i in [0:N] do
    let (k, g') := g.nat (N - i)
    g := g'
    a := a.swapIfInBounds i (i + k)
  return (Perm.ofList! a.toList, g)

/-- The suite. -/
def suite : TestM Unit := do
  -- IEEE toolkit: exact decode/re-encode, neighbours, printing round-trips
  let mut g := Tests.Rng.ofSeed 0x5EED
  let mut okRat := true
  let mut okNext := true
  let mut okPrint := true
  let mut okUlp := true
  for _ in [0:20000] do
    let (x, g') := randFinite g
    g := g'
    match IEEEFloat.toRat? x with
    | some q => if !(sameFloat (IEEEFloat.ofRat Float q) x || (x == 0 && q == 0)) then okRat := false
    | none => okRat := false
    if !(sameFloat (IEEEFloat.nextFloat (IEEEFloat.prevFloat x)) x) && x != 0 then okNext := false
    if !((parseFloat (Float.toJulia x)).map (sameFloat · x) |>.getD false) then okPrint := false
    let ax := x.abs
    if ax.isFinite && ax ≥ IEEEFloat.floatmin Float && ax < IEEEFloat.floatmax Float then
      -- ulp(x) is the gap above |x| unless |x| is a power of two approached from below
      if !(sameFloat (IEEEFloat.ulp x) (IEEEFloat.nextFloat ax - ax)) then okUlp := false
  check "ofRat ∘ toRat = id (20000 random floats)" okRat
  check "nextFloat ∘ prevFloat = id" okNext
  check "parse ∘ toJulia = id (shortest printing round-trips)" okPrint
  check "ulp = gap above |x|" okUlp
  -- correctly rounded division: ofFraction a b = a / b in IEEE arithmetic
  let mut okDiv := true
  for _ in [0:20000] do
    let (a, g1) := g.int (-1000000) 1000000
    let (b, g2) := g1.nat 1000000
    g := g2
    if b > 0 && !(sameFloat (IEEEFloat.ofFraction Float a (b + 1)) (Float.ofInt a / Float.ofNat (b + 1))) then
      okDiv := false
  check "ofFraction matches IEEE division" okDiv
  checkEq "eps(Float64)" (Float.toJulia (IEEEFloat.eps Float)) "2.220446049250313e-16"
  checkEq "eps(Float32)" (JuliaFloat.float32Repr (IEEEFloat.eps Float32)) "1.1920929f-7"
  checkEq "prevfloat(Inf)" (Float.toJulia (IEEEFloat.prevFloat (IEEEFloat.inf Float))) "1.7976931348623157e308"
  checkEq "floatmax(Float32)" (JuliaFloat.float32Repr (IEEEFloat.floatmax Float32)) "3.4028235f38"
  -- permutation group: sign is a homomorphism on random S6 pairs; orders divide 720
  let mut okSign := true
  let mut okOrder := true
  let mut okInv := true
  for _ in [0:500] do
    let (p, g1) := randPerm 6 g
    let (q, g2) := randPerm 6 g1
    g := g2
    if (p * q).sign != p.sign * q.sign then okSign := false
    if 720 % p.groupOrder != 0 || !(Perm.npow p p.groupOrder == 1) then okOrder := false
    if !(p * p⁻¹ == 1 && (p.div q) * q == p) then okInv := false
  check "sign(pq) = sign(p) sign(q) on S6" okSign
  check "p^order(p) = 1 and order | 720" okOrder
  check "inverses" okInv
  -- Limit bookkeeping: seeking back and forth is consistent
  let x : CountableVector Float := ⟨fun i => 1 / Float.ofNat (i * i), 10⟩
  let S := x.sum
  check "seek forth then back" (sameFloat ((S.seek 25).seek 10).last S.last)
  check "limitEps stops below ϵ" ((S.limitEps 1e-6).r ≤ 1e-6)
  check "Julia's limit(L, ϵ) length convention" ((S.limitEps 1e-6).n == S.n + ((S.limitEps 1e-6).n - S.n))
  -- clean vs Julia `isbounded`
  checkEq "isBounded (clean)" (isBounded ⟨#[1.0, 2.0]⟩) true
  checkEq "isbounded (Julia, inverted)" (Julia.isBounded ⟨#[1.0, 2.0]⟩) false

end Tests.AbstractAnalysis.Props
