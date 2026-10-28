# Talk notes: a verified port of Grassmann.jl (15–20 min)

A working outline for a verification audience. Every claim below names the
theorem, file or benchmark that backs it, so slides can be cut straight from
here and checked with `lake build`.

## One-line pitch

A Lean 4 port of Michael Reed's Grassmann.jl ecosystem that runs at Julia's
speed on many hot paths, matches Julia's golden outputs (almost all bit for bit),
and carries a proof chain from the bit tricks in the blade product down to the
loop that writes the result.

## Arc (minutes are rough)

1. **The object (2 min).** Geometric algebra in one slide: `e₁e₂ = −e₂e₁`,
   `eᵢ² = g(i)`, a multivector is `2ⁿ` coefficients indexed by bitmasks, and
   the product of blades is `±g · e_{a⊕b}` with the sign from a parity of bit
   counts. Julia's implementation is a dense pile of bit tricks and generated
   code; that is what makes it fast and what makes it worth verifying.

2. **The port and the oracle (3 min).** Julia is the oracle: goldens generated
   by `oracle/generate_all.jl` and compared in `lake test`. Speed:
   `docs/PERF.md` (ℝ3 batch sandwich 3.6 ns vs Julia 4.7 ns; CGA3 full product
   147 ns vs 149 ns; the losing cases and their four known causes are listed
   there too). Point: verification here is not paid for with a slow toy.

3. **The proof chain (8 min, the core).** Four links, each a different proof
   technique:

   | link | statement | technique | where |
   |---|---|---|---|
   | bits → sign | `reorderParity` (a branch-free prefix-xor scan, ~20 ALU ops) is the spec reordering sign on all 2¹²⁸ pairs of 64-bit masks | general proof | `DirectSum.Proofs.reorderParity_eq_spec` |
   | blade rule → spec | the implementation's blade product is the spec coefficient in every plain signature space of dimension ≤ 64 | general proof | `Grassmann.Proofs.General` |
   | plan → spec table | the reference kernel's plan is exactly the spec product table | `decide +kernel`, per space | `Grassmann.Proofs.Tables` (`*_mul_plan`) |
   | interpreter → spec product | running a spec-table plan computes the twisted convolution; the reference kernels of ℝ3, `diag(1,2,−3)`, STA and PGA3 return the Clifford product on every input | general proof + one kernel check | `Grassmann.Proofs.Interp` (`eval₂_eq_twist`, `R3_refMul`, …) |

   The spec itself (`Grassmann.Spec`) is small: coefficient functions on
   `BitVec n`, product as `twist (coef g)`, with associativity, the Clifford
   relation, reversion laws and the double Hodge star proved once. The
   transported laws (`Grassmann.Proofs.Transport`) then hold for the
   implementation's own operations in whole families of spaces.

   The interpreter link is the newest and the best slide: the theorem is
   stated about the actual tail-recursive loop (`Plan.eval₂`) the library
   runs, not a model of it. Its first layer (`get_eval₂`) holds for every
   coefficient type including `Float`, so it pins the exact order of floating
   point operations even where there is no algebraic theorem.

4. **Automation (2 min).** `clifford` and `grind [grassmann]` close identities
   by normalising to coordinates (`Tests.Proofs.TacticExamples`: Jacobi,
   Lagrange, rotor sandwiches in ℝ³, STA, PGA, ℝ⁵).

5. **What is not proved, honestly (2 min).** From `docs/PROOFS.md`, "Not
   covered": no floating-point error bounds; the generated straight-line
   kernels and typed `Chain` plans are tested, not proved; `pext`/`pdep`;
   left and conformal complements in general.

6. **Speculative (2–3 min).** Directions, in order of how soon they could be
   real:
   * translation validation of the generated kernels (each is a fixed
     polynomial, so `decide` on basis inputs plus a bilinearity proof of the
     emitter would close the last tested-only link for products);
   * floating-point error bounds for `eval₂` from its exact `Float` fold;
   * a bridge to Mathlib's `CliffordAlgebra` (DESIGN.md §8.5);
   * using the verified kernels as a target for LLM-written geometric code
     (the oracle and the spec give a two-sided check).

## Live demo candidates

* `#print axioms Grassmann.Proofs.Interp.STA_refMul`: three standard axioms,
  no `native_decide`.
* A `clifford` proof of the rotor sandwich in ℝ³ from `Tests/Proofs/TacticExamples.lean`.
* `lake exe bench --smoke` beside the Julia twin numbers.
