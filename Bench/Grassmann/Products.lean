import Bench.Grassmann.Common

/-!
# Typed operations of the generated kernels (DESIGN.md §5.2, docs/PERF.md)

Cases `grassmann/<space>/<op>` at `Float`, each over the `K = 1024` operands of a ring
(`Bench.Grassmann.Common`), against the same loops in `oracle/bench/grassmann.jl`. The call
sites are ordinary typed expressions (`a * b`, `v ⊘ R`, `~m`, ...) inside `spaceCases`, which is
`@[inline]`: at each concrete space its `Kernels` dispatch folds to the generated kernels
specialized at `Float`, exactly as in user code.

Groups (`CaseSet`): products and sandwiches; inner products (`⋅`, `⨼`, `∨`, `×`, `⊛`);
norms and inverses (`abs2`, `norm`, `inv`, `/`, `\`); linear combinations (`+`, `-`, scalar
multiples, mixed-kind promotion); unary maps (reverse, involutions, complements, grade
projections); and two harness floors (the sum of an operand, and the sum of a fresh copy of
one: the allocation every vector-valued Lean result pays, and a Julia isbits result does not).
-/

namespace Bench.Grassmann

open _root_.Grassmann DirectSum StaticVectors Bench

/-- `2.5` (a top-level constant, not a literal inside the loop: docs/PERF.md). -/
def c25 : Float := 2.5
/-- `1.5`. -/
def c15 : Float := 1.5

/-- Which case groups a space runs. -/
structure CaseSet where
  /-- Inner products (gap `grassmann/inner-products`). -/
  inner : Bool := true
  /-- `abs2` and `norm`. -/
  norms : Bool := true
  /-- Inverses and divisions (only where Julia's `inv` is defined for random operands). -/
  inverses : Bool := false
  /-- Spinor inverses and divisions (Julia's `inv(::Spinor)` is defined for random operands
  only when `(~s)s` is a scalar: `n ≤ 3`). -/
  spinorInverses : Bool := false
  /-- Linear combinations. -/
  linear : Bool := true
  /-- Unary maps beyond reverse and Hodge. -/
  unary : Bool := true
  /-- The harness floors. -/
  floors : Bool := true

/-- `space_cases% "label" V seed cs`: the cases of one space as a `BenchM Unit` program, written at
the concrete space `V` (a macro, so every operation is elaborated at concrete types as in user
code: sizes such as `halfDim V.n false` are closed terms, and each typed operation compiles to
its generated kernel specialized at `Float`). Rings are seeded from `seed`. -/
syntax (name := spaceCasesStx) "space_cases% " str term:max num term:max : term

macro_rules
  | `(space_cases% $label $V $seed $cs) => `(show Bench.BenchM Unit from do
      let n := ($V).n
      let p := s!"K={ringSize}"
      let k (s : String) := $label ++ "/" ++ s
      let M := ringOf (2 ^ n) ($seed * 16 + 1) (Multivector.mk (V := $V) (α := Float))
      let N := ringOf (2 ^ n) ($seed * 16 + 2) (Multivector.mk (V := $V) (α := Float))
      let S := ringOf (halfDim n false) ($seed * 16 + 3) (Half.mk (V := $V) (odd := false) (α := Float))
      let T := ringOf (halfDim n false) ($seed * 16 + 4) (Half.mk (V := $V) (odd := false) (α := Float))
      let U := ringOf (Leibniz.binomial n 1) ($seed * 16 + 5) (Chain.mk (V := $V) (G := 1) (α := Float))
      let W := ringOf (Leibniz.binomial n 1) ($seed * 16 + 6) (Chain.mk (V := $V) (G := 1) (α := Float))
      let C := ringOf (Leibniz.binomial n 2) ($seed * 16 + 7) (Chain.mk (V := $V) (G := 2) (α := Float))
      let H := ringOf (Leibniz.binomial n (n - 1)) ($seed * 16 + 8) (Chain.mk (V := $V) (G := n - 1) (α := Float))
      let J := ringOf (Leibniz.binomial n (n - 1)) ($seed * 16 + 9) (Chain.mk (V := $V) (G := n - 1) (α := Float))
      if ($cs : CaseSet).floors then
        case1 (k "sum of an operand") (fun (a : Multivector $V Float) => total a.v) M p
        case1 (k "copy of an operand") (fun (a : Multivector $V Float) =>
          (a.v.data.set! 0 (a.v.data.get! 1)).foldl (· + ·) 0) M p
      -- products and sandwiches
      case2 (k "Multivector*Multivector") (fun (a b : Multivector $V Float) => total (a * b).v) M N p
      case2 (k "Spinor*Spinor") (fun (s t : Spinor $V Float) => total (s * t : Spinor $V Float).v) S T p
      case2 (k "Chain1*Chain1") (fun (a b : Chain $V 1 Float) => total (a * b : Spinor $V Float).v) U W p
      case2 (k "Chain1∧Chain1") (fun (a b : Chain $V 1 Float) => total (a ∧ b : Chain $V 2 Float).v) U W p
      case2 (k "Chain2*Chain1") (fun (c : Chain $V 2 Float) (u : Chain $V 1 Float) => total (c * u : CoSpinor $V Float).v) C U p
      case2 (k "Multivector∧Multivector") (fun (a b : Multivector $V Float) =>
        total (a ∧ b : Multivector $V Float).v) M N p
      case2 (k "R*v*~R") (fun (R : Spinor $V Float) (v : Chain $V 1 Float) =>
        total (R * v * ~R : CoSpinor $V Float).v) S U p
      case2 (k "v ⊘ R") (fun (R : Spinor $V Float) (v : Chain $V 1 Float) => total (v ⊘ R : Chain $V 1 Float).v) S U p
      case2 (k "R >>> v") (fun (R : Spinor $V Float) (v : Chain $V 1 Float) =>
        total (R >>> v : Chain $V 1 Float).v) S U p
      -- inner products
      if ($cs : CaseSet).inner then
        case2 (k "Chain1⋅Chain1") (fun (a b : Chain $V 1 Float) => total (a ⋅ b).v) U W p
        case2 (k "Chain2⋅Chain1") (fun (c : Chain $V 2 Float) (u : Chain $V 1 Float) => total (c ⋅ u).v) C U p
        case2 (k "Chain1⨼Chain2") (fun (u : Chain $V 1 Float) (c : Chain $V 2 Float) => total (u ⨼ c).v) U C p
        case2 (k "Multivector⋅Multivector") (fun (a b : Multivector $V Float) =>
          total (a ⋅ b : Multivector $V Float).v) M N p
        case2 (k "Chain(n-1)∨Chain(n-1)") (fun (a b : Chain $V (n - 1) Float) => total (a ∨ b).v) H J p
        case2 (k "Multivector∨Multivector") (fun (a b : Multivector $V Float) =>
          total (a ∨ b : Multivector $V Float).v) M N p
        case2 (k "Chain1×Chain1") (fun (a b : Chain $V 1 Float) => total (a × b : Chain $V (n - (1 + 1)) Float).v) U W p
        case2 (k "Multivector⊛Multivector") (fun (a b : Multivector $V Float) =>
          total (a ⊛ b : Chain $V 0 Float).v) M N p
      -- norms and inverses
      if ($cs : CaseSet).norms then
        case1 (k "abs2 Multivector") (fun (a : Multivector $V Float) => total a.abs2.v) M p
        case1 (k "abs2 Spinor") (fun (s : Spinor $V Float) => total s.abs2.v) S p
        case1 (k "abs2 Chain1") (fun (u : Chain $V 1 Float) => total u.abs2.v) U p
        case1 (k "norm Multivector") (fun (a : Multivector $V Float) => Grassmann.norm a) M p
      if ($cs : CaseSet).inverses then
        case1 (k "inv Chain1") (fun (u : Chain $V 1 Float) => total u⁻¹.v) U p
        case2 (k "Chain1/Chain1") (fun (a b : Chain $V 1 Float) => total (a / b : Spinor $V Float).v) U W p
        case2 (k "Chain1\\Chain1") (fun (a b : Chain $V 1 Float) => total (a⁻¹ * b : Spinor $V Float).v) U W p
      if ($cs : CaseSet).spinorInverses then
        case1 (k "inv Spinor") (fun (s : Spinor $V Float) => total s⁻¹.v) S p
        case2 (k "Spinor/Spinor") (fun (s t : Spinor $V Float) => total (s / t : Spinor $V Float).v) S T p
      -- linear combinations
      if ($cs : CaseSet).linear then
        case2 (k "Multivector+Multivector") (fun (a b : Multivector $V Float) => total (a + b).v) M N p
        case2 (k "Chain1+Chain1") (fun (a b : Chain $V 1 Float) => total (a + b).v) U W p
        case2 (k "Spinor-Spinor") (fun (s t : Spinor $V Float) => total (s - t).v) S T p
        case1 (k "2.5*Multivector") (fun (a : Multivector $V Float) => total (c25 * a).v) M p
        case2 (k "2.5*Chain1+1.5*Chain1") (fun (a b : Chain $V 1 Float) => total (c25 * a + c15 * b).v) U W p
        case2 (k "Chain1+Multivector") (fun (u : Chain $V 1 Float) (b : Multivector $V Float) =>
          total (u + b : Multivector $V Float).v) U N p
        case2 (k "Chain1+Chain2") (fun (u : Chain $V 1 Float) (c : Chain $V 2 Float) =>
          total (u + c : Multivector $V Float).v) U C p
      -- unary maps
      case1 (k "reverse Multivector") (fun (a : Multivector $V Float) => total (~a).v) M p
      bench (k "reverse in place (m := ~m)") (ops := ringSize) (param := p) fun s =>
        let m := M[s % ringSize]!
        total (iterate (fun (a : Multivector $V Float) => ~a) m ringSize).v
      case1 (k "hodge Multivector") (fun (a : Multivector $V Float) => total (⋆a : Multivector $V Float).v) M p
      case1 (k "hodge Chain1") (fun (u : Chain $V 1 Float) => total (⋆u : Chain $V (n - 1) Float).v) U p
      if ($cs : CaseSet).unary then
        case1 (k "involute Multivector") (fun (a : Multivector $V Float) => total (involute a).v) M p
        case1 (k "clifford Multivector") (fun (a : Multivector $V Float) => total (clifford a).v) M p
        case1 (k "complementright Multivector") (fun (a : Multivector $V Float) =>
          total (complementRight a : Multivector $V Float).v) M p
        case1 (k "grade 2 of Multivector") (fun (a : Multivector $V Float) => total (gradePart a 2).v) M p
        case1 (k "even Multivector") (fun (a : Multivector $V Float) => total (even a : Spinor $V Float).v) M p)

end Bench.Grassmann
