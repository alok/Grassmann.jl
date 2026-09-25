import Tests.Wilkinson.Util
import Tests.Util.Random

/-!
Property tests (SplitMix64) and compile-time checks for the Wilkinson port:

* `BigFloat p` is correctly rounded (nearest, ties to even) at every precision,
  checked against exact rational arithmetic, and `BigFloat 53`/`BigFloat 24`
  agree with the hardware's `Float64`/`Float32` arithmetic;
* Wilkinson's premise, the forward error bound of floating-point evaluation:
  a Horner form of `p` evaluated in `Float64` satisfies
  `|fl(p)(x) - p(x)| ≤ γₖ · |p|(|x|)`, `γₖ = k·u/(1 - k·u)`, `u = 2⁻⁵³`, with `k`
  the number of floating-point operations and `|p|` the form with every sign
  made positive (`SyntaxTree.abs`), both sides computed exactly in `ℚ`;
* printing and parsing Julia expressions are inverse, and REDUCE-shaped forms
  denote the polynomial they came from.
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.Props

/-! ## Compile-time checks -/

-- Julia's parser shapes, as the quotation produces them
example : jl⟪a + b - c + d + e⟫ =
    .call "+" [.call "-" [.call "+" [.sym "a", .sym "b"], .sym "c"], .sym "d", .sym "e"] := rfl
example : jl⟪-2x^2⟫ = .call "*" [.int (-2), .call "^" [.sym "x", .int 2]] := rfl
example : jl⟪x^-2⟫ = .call "^" [.sym "x", .int (-2)] := rfl
-- call counts of the forms in Reed's examples
example : SyntaxTree.callcount jl⟪(x - 2)^9⟫ = 2 := by decide
example : SyntaxTree.callcount jl⟪((((x - 18) * x + 144) * x - 672) * x + 2016)⟫ = 7 := by decide
example : SyntaxTree.callcount jl⟪2x^2 - 1//2⟫ = 4 := by decide
-- REDUCE's gck2: a negative common factor survives only when the operands agree
example : Reduce.gck2 (-2) (-2) = -2 ∧ Reduce.gck2 (-4) (-6) = 2 ∧ Reduce.gck2 1 (-1) = 1 := by decide
-- the precision is part of the type: 7 has no 2-bit representation and rounds to even (8)
example : (BigFloat.ofInt 2 7 : BigFloat 2) = .finite false 2 2 := by decide
example : (BigFloat.ofInt 53 (2 ^ 53 + 1) : BigFloat 53) = BigFloat.ofInt 53 (2 ^ 53) := by decide
example : (BigFloat.ofInt 3 7 + BigFloat.ofInt 3 1 : BigFloat 3) = .finite false 4 1 := by decide
example : (BigFloat.ofInt 4 1 / BigFloat.ofInt 4 3 : BigFloat 4) = .finite false 11 (-5) := by decide

/-! ## Correct rounding of `BigFloat` -/

/-- Is `r` the round-to-nearest-even `p`-bit value of the exact `q`? -/
def isNearest {p : Nat} (r : BigFloat p) (q : Rat) : Bool :=
  match r, r.toRat? with
  | .finite _ m e, some rq =>
    let pow2 (k : Int) : Rat := if k ≥ 0 then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)
    let d := if q ≥ rq then q - rq else rq - q
    -- below a power of two the neighbour is half as far
    let half := if m == 2 ^ (p - 1) && (if rq ≥ 0 then q < rq else q > rq) then pow2 (e - 2) else pow2 (e - 1)
    d < half || (d == half && m % 2 == 0)
  | .zero _, _ => q == 0
  | _, _ => false

/-- A random finite dyadic `±m·2^e` as a `Float`. -/
def randDyadic : Tests.Gen Float := do
  let m ← Tests.Gen.nat (2 ^ 53)
  let e ← Tests.Gen.int (-60) 60
  let s ← Tests.Gen.nat 2
  let x := Float.scaleB (Float.ofNat (m + 1)) (e - 52)
  return if s == 0 then x else -x

/-- Check correct rounding of `+ - * /` at precision `p` on `n` random pairs. -/
def roundingAt (p : Nat) (n : Nat) (seed : Nat) : Bool :=
  let pairs := Tests.Gen.run seed (Tests.Gen.array n (do return (← randDyadic, ← randDyadic)))
  pairs.all fun (a, b) =>
    let A := BigFloat.ofFloat p a
    let B := BigFloat.ofFloat p b
    match A.toRat?, B.toRat? with
    | some qa, some qb =>
      isNearest (A + B) (qa + qb) && isNearest (A - B) (qa - qb) && isNearest (A * B) (qa * qb) &&
        (qb == 0 || isNearest (A / B) (qa / qb))
    | _, _ => false

/-! ## The forward error bound -/

/-- Floating-point operations in an expression (`n` arguments cost `n - 1`). -/
def opcount : JExpr → Nat
  | .call _ args => (args.length - 1) + go args
  | _ => 0
where
  /-- Over the arguments. -/
  go : List JExpr → Nat
    | [] => 0
    | a :: as => opcount a + go as

/-- Does the expression contain a power (not a `+ - *` evaluation)? -/
def hasPow : JExpr → Bool
  | .call op args => op == "^" || op == "/" || go args
  | _ => false
where
  /-- Over the arguments. -/
  go : List JExpr → Bool
    | [] => false
    | a :: as => hasPow a || go as

/-- A random dense integer polynomial of degree `2…9` (no zero coefficients, so its
Horner form has no powers), and a random `x ∈ ±[1/16, 4)`. -/
def randCase : Tests.Gen (Poly × Float) := do
  let d := 2 + (← Tests.Gen.nat 8)
  let mut cs : Array Rat := #[]
  for _ in [0:d + 1] do
    let c ← Tests.Gen.int 1 50
    let s ← Tests.Gen.nat 2
    cs := cs.push (if s == 0 then (c : Rat) else -(c : Rat))
  let m ← Tests.Gen.nat (2 ^ 52)
  let e ← Tests.Gen.int (-4) 1
  let s ← Tests.Gen.nat 2
  let x := Float.scaleB (Float.ofNat (2 ^ 52 + m)) (e - 52)
  return (Poly.mk' cs, if s == 0 then x else -x)

/-- `|fl(h)(x) - p(x)| ≤ γₖ |h|(|x|)` for the REDUCE Horner form `h` of `p`. -/
def boundHolds (p : Poly) (x : Float) : Bool :=
  let h := Reduce.horner (Reduce.expand (Reduce.toJExpr (Reduce.expandRF p)))
  if hasPow h then true else
  match (SyntaxTree.eval (.f64 x) (SyntaxTree.sub .f64 h)).toF64, JuliaBase.IEEEFloat.toRat? x,
      Poly.ofJExpr (SyntaxTree.abs h) with
  | v, some qx, some habs =>
    match JuliaBase.IEEEFloat.toRat? v with
    | some qv =>
      let k := opcount h
      let u : Rat := 1 / ((2 ^ 53 : Nat) : Rat)
      let γ := (k : Rat) * u / (1 - (k : Rat) * u)
      let err := qv - p.eval qx
      let err := if err < 0 then -err else err
      err ≤ γ * habs.eval (if qx < 0 then -qx else qx)
    | none => false
  | _, _, _ => false

/-! ## Expressions -/

/-- A random polynomial-like Julia expression. -/
partial def randExpr (depth : Nat) : Tests.Gen JExpr := do
  let k ← Tests.Gen.nat (if depth == 0 then 3 else 9)
  match k with
  | 0 => return .sym "x"
  | 1 => return .int ((← Tests.Gen.int (-20) 20))
  | 2 => return .f64 (Float.ofInt (← Tests.Gen.int (-999) 999) / 8)
  | 3 => return .call "+" [← randExpr (depth - 1), ← randExpr (depth - 1), ← randExpr (depth - 1)]
  | 4 => return .call "-" [← randExpr (depth - 1), ← randExpr (depth - 1)]
  | 5 => return .call "*" [← randExpr (depth - 1), ← randExpr (depth - 1)]
  | 6 => return .call "^" [← randExpr (depth - 1), .int ((← Tests.Gen.nat 3) + 2)]
  | 7 =>
    -- Julia's parser reads `-4` as a literal, never as `-(4)`, and prints both as `-4`
    match ← randExpr (depth - 1) with
    | .lit (.int n) => return .int (-n)
    | .lit (.f64 v) => return .f64 (-v)
    | a => return .call "-" [a]
  | _ => return .call "/" [← randExpr (depth - 1), .int ((← Tests.Gen.nat 9) + 1)]

/-- The suite. -/
def suite : TestM Unit := do
  for (p, seed) in [(2, 1), (3, 2), (24, 3), (53, 4), (64, 5), (113, 6), (256, 7)] do
    check s!"BigFloat {p}: + - * / correctly rounded (2000 pairs)" (roundingAt p 2000 seed)
  -- BigFloat 53 is IEEE double (normal range), BigFloat 24 is IEEE single
  let pairs := Tests.Gen.run 11 (Tests.Gen.array 5000 (do return (← randDyadic, ← randDyadic)))
  check "BigFloat 53 ≡ Float64 on + - * /" <| pairs.all fun (a, b) =>
    let (A, B) := (BigFloat.ofFloat 53 a, BigFloat.ofFloat 53 b)
    sameFloat (A + B).toFloat (a + b) && sameFloat (A - B).toFloat (a - b) &&
      sameFloat (A * B).toFloat (a * b) && sameFloat (A / B).toFloat (a / b)
  check "BigFloat 24 ≡ Float32 on + - * /" <| pairs.all fun (a, b) =>
    let (a, b) := (a.toFloat32, b.toFloat32)
    let (A, B) := (BigFloat.ofFloat32 24 a, BigFloat.ofFloat32 24 b)
    sameF32 (A + B).toFloat32 (a + b) && sameF32 (A - B).toFloat32 (a - b) &&
      sameF32 (A * B).toFloat32 (a * b) && sameF32 (A / B).toFloat32 (a / b)
  -- the forward error bound behind the Stieltjes bound
  let cases := Tests.Gen.run 21 (Tests.Gen.array 3000 randCase)
  let bad := cases.toList.filter fun (p, x) => !boundHolds p x
  check s!"Horner forward error ≤ γₖ |p|(|x|) ({cases.size} random cases)" bad.isEmpty
    s!"{bad.length} violations"
  -- Julia printing and parsing are inverse
  let exprs := Tests.Gen.run 31 (Tests.Gen.array 3000 (randExpr 4))
  let badE := exprs.toList.filter fun e =>
    match JExpr.parse e.toJulia with
    | .ok p => p != e
    | .error _ => true
  check s!"parse ∘ string = id ({exprs.size} random expressions)" badE.isEmpty
    s!"first: {(badE.head?.map JExpr.toJulia).getD ""}"
  -- the REDUCE forms denote the same polynomial; factors multiply back
  -- (degree ≤ 10 keeps the factorization cheap)
  let polys := (Tests.Gen.run 41 (Tests.Gen.array 800 (randExpr 3))).filter fun e =>
    match Poly.ofJExpr e with
    | some p => p.degree ≤ 10
    | none => false
  let badR := polys.toList.filter fun e =>
    match Poly.ofJExpr e with
    | some p => ![Reduce.expand e, Reduce.horner e, Reduce.factor e].all (Poly.ofJExpr · == some p)
    | none => false
  check s!"expand/horner/factor preserve the polynomial ({polys.size} random expressions)" badR.isEmpty
    s!"first: {(badR.head?.map JExpr.toJulia).getD ""}"
  let badF := polys.toList.filter fun e =>
    match Poly.ofJExpr e with
    | some p =>
      if p.isZero then false else
      let (N, _) := p.toZ
      let fz := factorZ N
      let prod := fz.factors.foldl (fun acc (f, k) => acc * Poly.pow (Poly.ofZ f) k)
        (Poly.const fz.content * Poly.pow Poly.X fz.xpow)
      !(prod == Poly.ofZ N)
    | none => false
  check "content · ∏ fᵢ^eᵢ · x^m = N" badF.isEmpty
  -- Reed's experiment on a factorizable cubic: exprval and the error values agree
  checkEq "testpoly((x-1)(x-2)(x-3))" (testpoly Reduce.cas jl⟪(x-1)*(x-2)*(x-3)⟫ .f64) (true, true, true)

end Tests.Wilkinson.Props
