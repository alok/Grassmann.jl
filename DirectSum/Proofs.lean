import DirectSum.Proofs.Sign
import DirectSum.Proofs.Metric
import DirectSum.Proofs.UInt64

/-!
# DirectSum.Proofs: the blade sign rules, proved for every dimension

Theorems about the bit-level sign rules of `DirectSum.Bits`/`DirectSum.Parity`
(docs/PROOFS.md has the full inventory):

* `DirectSum.Proofs.Sign`: the reordering sign `σ(a, b)` (inversion count mod 2)
  on `Nat` masks of any width: bilinearity over `𝔽₂`, the 2-cocycle identity
  `sigma_cocycle`, the swap identity `sigma_add_sigma_swap`
  (`σ(a,b) + σ(b,a) ≡ |a||b| - |a∧b|`), the reversion sign `sigma_self`, and
  agreement with the repository's naive `reorderParitySpec`.
* `DirectSum.Proofs.Metric`: diagonal metric factors over any
  `Lean.Grind.CommRing`, their multiplicativity (`metricFactor_cocycle`) and the
  twisted cocycle of the blade-product coefficient (`bladeCoef_cocycle`);
  signature and zero metrics.
* `DirectSum.Proofs.UInt64`: the branch-free kernels `Bits.parity`,
  `Bits.prefixParity`, `Bits.reorderParity` and Julia's `parityjoin` equal the
  specification on **all** `UInt64` masks (`reorderParity_eq_spec`,
  `signOf_parityjoin`).

No `sorry`, no axioms beyond Lean's standard three, no `native_decide`.
-/
