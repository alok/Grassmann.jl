# Checked R3 storage decoding and an exact rational rotor

This optional module closes a concrete execution boundary before a CAD or runtime
adapter chooses an ABI. It reuses the existing Grassmann representations and
generated kernels. Attribution: independent Lean port of Michael Reed/chakravala's
Grassmann ecosystem; the extra packet is an independent exact coordinate reference,
not a replacement for the pinned Julia oracle fixtures.

## Checked representation decoding

`Grassmann.Kernel.R3Rotor.decode` returns `Option (Multivector ℝ3 α)` under only
`[Coeff α]`. It returns `some x.toDense` when `TA.WF x` holds, and `none` otherwise.
The guard rejects symbolic `Infinity`, `Phasor`, and invalid stored blade masks.
`TA.IsLinear` would admit invalid masks, while the unchecked `TA.toDense` observer
uses placeholder zeros for symbolic values and discards invalid masks.

`normalize x := (decode x).map TA.multi` preserves the complete checked observation:

```lean
(normalize x).bind decode = decode x
```

This copying theorem requires no zero-add, associativity, commutation, or ring laws.
The scalar bridge reuses `R3TopPairing.scalar_coeff`: canonical stored `Chain0 q`
and raw `Single0 q` agree at every `UInt64` mask and in complete checked decoding,
but remain structurally distinct, including at zero and unit coefficients. A
lawless test whose coefficient zero is `5` detects accidental literal-zero padding.
The existing sufficient `zeroAdd` premise for zero-first reference accumulation
belongs to that separate operation theorem, not to coefficient copying.

`WF` checks representation well-formedness. It admits stored Float NaN and infinity;
it does not certify finite geometry, Float field laws, or congruence of every
operation after normalization. The complete dense observation theorem also does
not establish a generic decoding map into the abstract `Spec.Cl` model.

## Actual generated rational action

The space is positive Euclidean R3 with `e1²=e2²=e3²=1` and `e12=e1*e2`.
The fixed rotor is `r = 3/5 + (4/5)e12`. Exact layouts are:

| Storage | Zero-based blade masks |
| --- | --- |
| Chain1 vector | `[1,2,4]` |
| Even rotor | `[0,3,5,6]` |
| Odd full sandwich | `[1,2,4,7]` |
| Full multivector | `[0,1,2,4,3,5,6,7]` |

Full storage is grade-major; numeric-mask buffer order is different.
`rotor_reverse` proves actual reversion and Clifford conjugation agree.
`rotor_unit` proves both actual typed unit products.

For arbitrary `x y z : Rat`, the concrete generated projected action satisfies

```text
r >>> [x,y,z] = [(-7*x+24*y)/25, (-24*x-7*y)/25, z].
```

The opposite convention `[x,y,z] ⊘ r = reverse(r)*v*r` has coordinates
`[(-7*x-24*y)/25, (24*x-7*y)/25, z]`.
`fullAction_formula` separately proves the complete two-product odd result is
`[x',y',z,0]`, including its trivector slot. This supplies the missing grade-leakage
check that a projected result alone cannot provide. `coordinates_norm` proves
the exact matrix preserves squared Euclidean length for every rational input.

These proofs unfold the actual emitted fused and binary bodies and their packed
writes. Concrete definitions freeze both `Kernels` and the higher-priority
`SandwichKernels`; replacing only `Kernels` does not replace fused sandwich
dispatch. The tests replace each relevant provider independently. Existing
abstract Clifford normalization and isometry theory stays separate. No general
`Plan.eval₂` refinement, arbitrary-rotor theorem, or Float field theorem is added.

## Reusable exact packet

[`../fixtures/r3-rational-rotor.json`](../fixtures/r3-rational-rotor.json) is an
additive, content-addressed packet for downstream adapters. It records operation
conventions, dimension and metric, all four storage orders, exact reduced
`{"num":"...","den":"..."}` rational coefficients, source baseline and module
SHA256, assumptions, and proof-versus-runtime boundaries. Twelve inputs cover
zero, each basis axis, signs, fractions, mixed coordinates, and cancellation.
Expected outputs come from an independent Python `Fraction` coordinate matrix.
The packet's final Git commit is supplied externally to avoid self-reference.

Its actual-library observation check compares 216 typed output coefficients and
192 named dynamic dense coefficients without Float conversion. This is finite
runtime evidence alongside the universal
Rat proofs. It verifies the packet against the library, not a downstream ABI,
calculator, Hegel runtime, or Notebook adapter.

## Validation and remaining boundaries

All execution ran serially at nice priority at least 10 with `LEAN_NUM_THREADS=2`.
No Julia or downstream adapter execution was added by this slice.

| Check | Result |
| --- | --- |
| Focused RotorDecode suite | 223 passed, 0 failed |
| Warning-free native test build | 1,182 jobs |
| Native Dynamic suite | 59,788 passed, 0 failed |
| Warning-free full build | 1,264 jobs |
| Full `lake test` | 3,481,018 passed, 0 failed |
| Axiom audit | 534 unique declarations: 494 retained and 40 new |
| Mutation controls | 12 executed sites detected |
| Direct kernel false-contract checks | 13 type-mismatch rejections |
| Elaboration negatives | 3 rejections |
| Independent packet/library comparison | 12 cases, 408 output coefficients, 36 inputs |

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The
elaboration negatives reject `Field Float`, `LawfulCoeff Float`, and treating
the checked Option-valued decoder as an unchecked multivector. Mutation sites
exercise orientation, omitted reverse, cross-term signs, denominator, wrong
plane, z sign, replaced fused provider, symbolic/domain guards, and literal-zero
padding. The wrong-plane kernel certificate checks the false rotor-input equality;
its output mutation is tested at runtime. The nonunit kernel certificate rejects
the doubled rotor's false unit premise, while runtime execution checks its squared
length counterexample `224 != 14`. Two timed-out draft certificates were excluded
from negative evidence. Only explicit kernel type mismatches count.

Local execution receipts and source review artifacts include
`/tmp/r3-cad-final-evidence.json`, `/tmp/r3-cad-audit-evidence.json`,
`/tmp/r3-cad-controls-verified.receipt.json`, and
`/tmp/r3-rational-rotor-engine-evidence.json`. The module SHA256 is
`c305b77cf837e8fc085c65e4325999b011fa27878e34558b2dd29fe358a8b21c`;
the packet SHA256 is
`16d1a15cb97342c85d83da7fc895845c65601ccd564ea40d2a0a7e8074af5908`.
The separate final commit receipt binds these bytes to the completed local commit.

The next mathematical boundary is a decoded exact vector/full-sandwich bridge
into the existing Euclidean `Cl` model. General interpreter refinement, broader
rotor construction, PGA translation and rigid composition, numeric nonfinite
policy, portable ABI packing, GPU execution, and regularized CSG each remain
separate work. The contraction parity ledger remains unchanged.
