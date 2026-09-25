import AbstractAnalysis.IEEE
import AbstractAnalysis.Show
import AbstractAnalysis.Countable
import AbstractAnalysis.Sequence
import AbstractAnalysis.Metric
import AbstractAnalysis.Limit
import AbstractAnalysis.Sets
import AbstractAnalysis.Magma
import AbstractAnalysis.Perm

/-!
# AbstractAnalysis

Lean port of Michael Reed's `AbstractAnalysis.jl` (v0.2.2): lazy countable
sequences, memoized recurrences, `Limit` objects for iterated maps, metrics and
convergence predicates, countable sets, finite magmas and permutation groups.
See `docs/port-notes/small-algebra.md` §2.5, §4.5.

Scalars print, compare and do complex arithmetic through `JuliaBase`
(`JuliaShow`, `F64.isapprox`, `JuliaBase.Complex`); `AbstractAnalysis.IEEE` holds
the exact IEEE toolkit `JuliaBase` does not have yet.

## What Cartan uses

Cartan.jl imports these names (Cartan.jl:36-43, 250, 513-582;
`docs/port-notes/cartan-core.md` §4.14). They are generic in the state type, so a
`TensorField` state plugs in with its own metric and slice storage:

| Julia | Lean |
|---|---|
| `Limit`, `residual`, `counter`, `initial`/`final` | `Limit S V` (fields `v0`, `v`, `n`, `r`, `step`), `Limit.residual` |
| `orbit(f, x, ϵ)`, `orbit(f, x, k)`, `orbiterror` | `orbit`, `orbitN`, `orbitError`, `orbitNTrace` |
| `orbithold` | `orbitHold` |
| `FixedCycle` | `FixedCycle` (`run`, `withLen`) |
| `collect(::Limit)` into growable storage | `Limit.collect`, `Limit.collectSeq` |
| `SequenceArray(storage, counter)` (Cartan: `ElasticArray` + `(u,k) -> f(extract(u,k-1))`) | `SequenceArray σ S` over any `LastDimStorage σ S` (`Array S`, `FloatArray`, `SlabArray` for stacked field slices), `resize`, `take` |
| `extract`, `assign!`, `resize_lastdim!` | `LastDimStorage.extract`, `.lastDim`, `.push` |
| `supnorm`, `infnorm`, `maxabs`, `minabs` | `supnorm`, `infnorm`, `maxabs`, `minabs` (via `Normed α`) |
| `residuals`, `lipschitz`, `distance` | `residuals`, `lipschitz` (the distance is an explicit argument or `Metric α`) |
| `derivative` | `derivative`, `derivative2` (Float; Cartan extends it to fields) |
| `CountableVector`, `CountableArray` | `CountableVector α`, `CountableArray α N` (rank in the type) |
-/
