/-
Tests for `StaticVectors`: oracle goldens on `Values{N,Float64}` (bitwise, `norm(a, 3)`
included now that it goes through Julia's own `^`), the StaticVectors README and
port-notes §6.4 facts, and compile-time checks on exact entries.
-/
import StaticVectors
import Tests.AbstractTensors.Harness
import Tests.AbstractTensors.Golden

namespace Tests.AbstractTensors.StaticVectorsTests

open StaticVectors JuliaBase

/-! ### Compile-time checks (exact entries, kernel-evaluated) -/

/-- `Values(1, 2, 3)`. -/
def v1 : Values Int 3 := .ofFn fun i => i.1 + 1

example : v1.sum = 6 := by decide
example : v1.prod = 6 := by decide
example : (Values.ofFn (n := 0) fun _ => (5 : Int)).sum = 0 := by decide
example : (Values.ofFn (n := 0) fun _ => (5 : Int)).prod = 1 := by decide
example : v1.cumsum.toList = [1, 3, 6] := by decide
example : v1.cumprod.toList = [1, 2, 6] := by decide
example : (v1.accumulate (· - ·)).toList = [1, -1, -4] := by decide
example : v1.reverse.toList = [3, 2, 1] := by decide
example : (Values.ofFn (n := 3) fun i => ([1, 4, 9] : List Int)[i.1]!).diff.toList = [3, 5] := by decide
example : (v1.append (Values.ofFn (n := 2) fun i => (i.1 : Int) + 4)).toList = [1, 2, 3, 4, 5] := by decide
example : v1.maximum = 3 := by decide
example : v1.minimum = 1 := by decide
example : v1.dot v1 = 14 := by decide
example : v1.count (· % 2 == 0) = 1 := by decide
example : v1.contains 2 = true := by decide
example : (Values.replicate (n := 2) (0 : Int)).isZero = true := by decide
example : (v1.gather (Values.ofFn (n := 4) fun i => ([2, 0, 0, 1] : List (Fin 3))[i.1]!)).toList =
    [3, 1, 1, 2] := by decide
example : (v1.scatter (Values.ofFn (n := 2) fun i => ([0, 2] : List (Fin 3))[i.1]!)
    (Values.ofFn fun i => ([7, 8] : List Int)[i.1]!)).toList = [7, 2, 8] := by decide
example : (v1.foldl (· - ·) 10) = 4 := by decide
example : ((2 : Int) * v1).toList = [2, 4, 6] := by decide
example : (v1 - v1).toList = [0, 0, 0] := by decide
example : compare v1 (v1.set 2 4) = .lt := by decide
example : (Values.cross (Values.ofFn fun i => ([1, 0, 0] : List Int)[i.1]!)
    (Values.ofFn fun i => ([0, 1, 0] : List Int)[i.1]!)).toList = [0, 0, 1] := by decide

/-! ### Oracle goldens -/

/-- Pack a golden bit array into a `Values Float n` and continue. -/
def withValues {β : Type} (a : Array UInt64) (k : {n : Nat} → Values Float n → β) : β :=
  k (Values.ofFn (n := a.size) fun i => fb a[i])

/-- The results of the unary golden functions, as a list of floats. -/
def unary (name : String) {n : Nat} (v : Values Float n) : Option (List Float) :=
  match name with
  | "sum" => some [v.sum]
  | "prod" => some [v.prod]
  | "maximum" => match n, v with | 0, _ => none | _ + 1, v => some [v.maximum]
  | "minimum" => match n, v with | 0, _ => none | _ + 1, v => some [v.minimum]
  | "cumsum" => some v.cumsum.toList
  | "cumprod" => some v.cumprod.toList
  | "accumulate-" => some (v.accumulate (· - ·)).toList
  | "reverse" => some v.reverse.toList
  | "diff" => match n, v with | 0, _ => none | _ + 1, v => some v.diff.toList
  | "norm" => some [v.norm]
  | "norm1" => some [v.normP 1]
  | "normInf" => some [v.normP Float.inf]
  | "norm3" => some [v.normP 3]
  | "normalize" => some v.normalize.toList
  | "normalize1" => some (v.normalizeP 1).toList
  | "neg" => some (-v).toList
  | "scale2.5" => some (v * (2.5 : Float)).toList
  | "div3" => some (v / (3 : Float)).toList
  | _ => none

/-- The results of the binary golden functions. -/
def binary (name : String) {n : Nat} (v w : Values Float n) : Option (List Float) :=
  match name with
  | "dot" => some [v.dot w]
  | "add" => some (v + w).toList
  | "sub" => some (v - w).toList
  | "vcat" => some (v.vcat w).toList
  | "isapprox" => some [if v.isapprox w then 1 else 0]
  | "isapproxself" => some [if v.isapprox (v.map (· + 1e-12)) then 1 else 0]
  | _ => none

/-- Compare lists of floats bitwise (or within `k` ulps). -/
def listClose (k : Nat) (xs ys : List Float) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (x, y) => ulpClose k x y

/-- Run the StaticVectors goldens and facts. -/
def suite : TestM Unit := do
  for (name, a, r) in Golden.svUnary do
    let want := r.toList.map fb
    match withValues a (unary name) with
    | none => check false fun _ => s!"sv {name}: not applicable to length {a.size}"
    | some got =>
      check (listClose 0 got want) fun _ => s!"sv {name}({a.toList.map fb}): got {got}, want {want}"
  for (name, a, b, r) in Golden.svBinary do
    let want := r.toList.map fb
    let got : Option (List Float) :=
      if h : b.size = a.size then
        withValues a fun {n} v =>
          if hn : n = a.size then
            binary name v (Values.ofFn (n := n) fun i => fb (b[i.1]'(by omega)))
          else none
      else none
    match got with
    | none => check false fun _ => s!"sv {name}: shape mismatch"
    | some got => check (listClose 0 got want) fun _ => s!"sv {name}: got {got}, want {want}"
  -- README and port-notes §6.4 facts
  let v2 : Values Float 3 := .ofFn fun i => Float.ofNat (i.1 + 1)
  check ((v2 + v2).toList == [2, 4, 6]) fun _ => "v2 + v2"
  check (same (Values.ofFn (n := 2) fun i => ([3.0, 4.0] : List Float)[i.1]!).norm 5) fun _ => "norm(3,4)"
  let big : Values Float 2 := .replicate 1e200
  check (big.norm == Float.inf) fun _ => "norm(1e200,1e200) == Inf (no scaling)"
  let n34 := (Values.ofFn (n := 2) fun i => ([3.0, 4.0] : List Float)[i.1]!).normalize
  check (same (n34.get 0) 0.6000000000000001 && same (n34.get 1) 0.8) fun _ => s!"normalize(3,4) = {n34}"
  let mz : Values Float 2 := .ofFn fun i => ([0.0, -0.0] : List Float)[i.1]!
  check (same mz.maximum 0.0 && same mz.minimum (-0.0)) fun _ => "max/min of ±0"
  let wn : Values Float 3 := .ofFn fun i => ([1.0, Float.nan, 3.0] : List Float)[i.1]!
  check wn.maximum.isNaN fun _ => "maximum propagates NaN"
  check (same (Values.ofFn (n := 1) fun _ => (-0.0 : Float)).sum (-0.0)) fun _ => "sum(-0.0) = -0.0"
  check (toString (Values.ofFn (n := 3) fun i => (i.1 : Int) + 1) == "[1, 2, 3]") fun _ => "print"
  check ((countvalues 1 4).toList == [1, 2, 3, 4]) fun _ => "countvalues"
  check ((evens 1 6).toList == [1, 3, 5]) fun _ => "evens"
  check (F64.isapprox 1.0 (1.0 + 1e-9) && !F64.isapprox 1.0 1.001) fun _ => "isapprox"
  check (same (F64.max (-0.0) 0.0) 0.0 && same (F64.min 0.0 (-0.0)) (-0.0)) fun _ => "Julia max/min"
  -- Julia 1.13: `isapprox(x, y)` on `Float32` is `true` for these pairs, which sit exactly
  -- where `rtol*max(|x|,|y|)` rounds up in `Float32` (a `Float64` product says `false`).
  for (x, y) in [(0x3ebd2143, 0x3ebd31fc), (0x40b9d107, 0x40b9e175), (0x3fba14e3, 0x3fba2557),
      (0x412786c5, 0x41279595)] do
    let x := Float32.ofBits x
    let y := Float32.ofBits y
    check (JApprox.isapprox x y 0 (JApprox.rtolDefault Float32) false) fun _ =>
      s!"isapprox(Float32) {x} {y}"

end Tests.AbstractTensors.StaticVectorsTests
