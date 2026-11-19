# Exact original-Nat mask ingress

Import `Grassmann.MaskIngress` explicitly. This optional boundary module reuses
the existing executable UInt64 masks, BitVec Clifford specification, conversion
proof bridge, and typed blade grade checks. Attribution: independent Lean port
of Michael Reed/chakravala's Grassmann ecosystem. Existing unchecked APIs and
pinned Julia fixtures retain their semantics.

## Public entrypoints

| API | Input and result | Admission contract |
| --- | --- | --- |
| `bitVec? n raw` | `Nat → Option (BitVec n)` | `raw < 2^n` |
| `word? n raw` | `Nat → Option UInt64` | `n ≤ 64` and `raw < 2^n` |
| `blade? (V := V) (G := G) raw` | `Option (Submanifold V G)` | exact word admission, then existing grade/high-bit check |
| `single? (V := V) (G := G) raw value` | `Option (Single V G α)` | same mask admission, preserving `value : α` |

The check applies to the original unbounded natural number before any narrowing.
For example, `word? 3 (2^64+1)` returns `none`; converting that input first would
produce UInt64 `1`, which existing R3 blade checks accept. Likewise ordinary
`9#3` wraps to `1`, while `bitVec? 3 9` rejects it. Proof-bounded literals may use
`BitVec.ofNatLT raw h` or scoped `raw#'h`, with `h : raw < 2^n`.

Semantic BitVec widths can exceed 64: `bitVec? 65 (2^64+1)` preserves that value.
Only the executable-word adapter rejects widths above 64, even for original zero.
At width zero the sole admitted mask is scalar zero. For every width, `2^n-1`
is the largest admitted value and `2^n` is the first rejected value.

## Proven contracts

`bitVec?_of_lt` and `bitVec?_toNat` certify successful exact construction.
`bitVec?_eq_none_iff` states rejection iff `2^n ≤ raw`.
`bitVec?_roundTrip` accepts every already proof-bounded mask's natural value.

`word?_of_lt` constructs through `Grassmann.Proofs.mask`, whose existing
`toNat_mask` proves exact conversion for `n ≤ 64`. `word?_sound` states every
accepted word has compatible width, original semantic bounds, and
`word.toNat = raw`. `word?_eq_none_iff` characterizes rejection as
`64 < n ∨ 2^n ≤ raw`. `word?_bridge` and `word?_roundTrip` certify both proof-bounded
BitVec ingress and width-bounded existing-word round trips.

`blade?_sound` additionally proves `popcount blade.bits = G`.
`single?_sound` proves the same mask/width/grade facts and exact coefficient
equality. Coefficient copying requires no `Coeff` instance or algebraic laws.
The typed helpers delegate to existing `Submanifold.ofBits?` and `Single.ofBits?`;
the new proofs use a small compositional Option/Boolean guard lemma rather than
normalizing the bit operations inside dependent case splits.

## Integration

Keep parsed masks as unbounded `Nat` values until checked admission. A parser
accepting signed numbers must reject negatives before producing a Nat; this API
does not reinterpret negative integers. Match on the Option result and report
admission failure at the external boundary. Use `word?` for an existing word-based
consumer, or the typed helpers when the expected algebra and grade are known.
With `open Grassmann DirectSum`, the entrypoint expressions are:

```lean
MaskIngress.blade? (V := ℝ3) (G := 2) 3
MaskIngress.single? (V := ℝ3) (G := 2) 3 (-2/3 : Rat)
```

Existing UInt64 inputs can retain their existing checked constructors; their
already-lost preconversion bits cannot be recovered. Mask numerical value also
does not equal grade-major packed storage position. The word width bound is 64,
while `TensorBundle.valid` has a separate printable descriptor bound of 62.
Mask admission does not prove descriptor/metric validity or change that policy.

Exterior membership masks remain separate from tangent multiindices and bounded
Leibniz/Taylor order. No mesh parser, connectivity or solid validation, bundle
payload contract, coefficient-law instance, dense allocation policy, ABI, or GPU
implementation is added by this slice.

## Validation

All compiler execution ran serially at nice priority at least 10 with
`LEAN_NUM_THREADS=2`. Final gates passed:

| Check | Result |
| --- | --- |
| Focused adversarial suite | 112 passed, 0 failed |
| Warning-free native build | 1,186 jobs |
| Native Dynamic suite | 59,900 passed, 0 failed |
| Warning-free full build | 1,268 jobs |
| Full `lake test` | 3,481,130 passed, 0 failed |
| Axiom audit | 555 declarations: 534 retained and 21 new |
| Executed mutations | 5 detected |
| Direct kernel false certificates | 6 type-mismatch rejections |
| Elaboration negatives | 3 rejections |

The runtime cases cover widths 0, 1, 3, 8, 62, 63, 64, 65 and 128; exact maximum,
first overflow and larger overflow; `2^64+1`; unchecked wrapping controls; static
grade rejection; rational and operation-free payload copying; and Float signed-zero
bits. Universal proof consumers separately use the preservation and rejection
theorems with arbitrary inputs.

Mutations narrow before checking, admit the first overflow, omit word-width
compatibility, bypass grade admission, or replace the coefficient. Kernel negatives
reject false admitted results for huge original input, incompatible width, first
overflow, zero-width overflow, wrong grade and wrong coefficient. Elaboration
negatives reject an impossible proof-bound literal and treating Option-valued word
or blade ingress as unchecked data. Only explicit kernel type mismatches count;
timed-out proof drafts and parser/elaboration mistakes were excluded from those six.
The audit uses only `propext`, `Classical.choice` and `Quot.sound`; no new coefficient
laws, custom axioms or native proof oracle were added.

The final scope preserves 1,625 prior tracked files byte-for-byte. The only existing
file modified is Dynamic suite registration. Preserved files include all 377 existing
goldens, the d48a1669 rotor source/packet,
legacy kernels and dependency pins. The 2,100 existing refs are preserved, with
only the current local branch advancing at commit. Local receipts are
`/tmp/mask-ingress-final-evidence.json`, `/tmp/mask-ingress-audit-evidence.json`,
`/tmp/mask-ingress-controls.receipt.json`, and the separate post-commit preservation
receipt. No new Julia parity claim or mesh import accompanies this additive API.
