import Grassmann.Batch.Elab

/-!
# Batches of typed elements: `Batch X`, `batch%`, `batchInto%`

A `Batch X` holds `len` elements of a typed container `X` (`Chain V G Float`,
`Half V p Float`, `Multivector V Float`) in one flat `FloatArray`, element-major (element `i`
is `data[i·k, …, i·k + k - 1]` in `X`'s storage order, `k` its storage size): the layout of
Julia's `Vector{Chain{V,G,Float64}}`, whose `isbits` elements sit inline.

`batch% fun (x₁ : X₁) … (xₘ : Xₘ) => e` compiles the typed-algebra expression `e`, once, into a
loop over batches: a function `Batch X₁ → … → Batch Xₘ → Batch Y` (`Y` the type of `e`). The
loop body is `e` fused at elaboration time exactly as by `fused%` (`Grassmann.Fuse`: the
generated kernels' plans in their summation order, one straight-line block, common
subexpressions shared), reading its operands' coefficients from the input arrays and writing
its result's into the output array: no allocation per element, one output array per batch.
`batchInto% f out x₁ … xₘ` writes into `out`'s storage instead (in place when `out` is
exclusive and of the right size): no allocation at all, Julia's `map!(f, out, xs…)`.

Element `i` of the result is `e` at element `i` of every input (the shortest input sets the
length), bit for bit up to the sign of zero (`Tests/Fuse/Batch.lean`).

```lean
open Grassmann in
def rotateAll : SpinorArray ℝ3 → ChainArray ℝ3 1 → HalfArray ℝ3 true :=
  batch% fun (R : Spinor ℝ3 Float) (v : Chain ℝ3 1 Float) => R * v * ~R
```
-/
