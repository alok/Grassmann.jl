import AbstractAnalysis.JuliaFloat
import AbstractAnalysis.Show
import AbstractAnalysis.Countable
import AbstractAnalysis.Sequence
import AbstractAnalysis.Metric
import AbstractAnalysis.Limit

/-!
# AbstractAnalysis

Lean port of Michael Reed's `AbstractAnalysis.jl` (v0.2.2): lazy countable
sequences, memoized recurrences, `Limit` objects for iterated maps, metrics and
convergence predicates, countable sets, finite magmas and permutation groups.
See `docs/port-notes/small-algebra.md` §2.5, §4.5.
-/
