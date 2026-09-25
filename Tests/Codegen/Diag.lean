/-
Kernels of a diagonal-metric space, `D!"1,2,-3"`: the non-unit metric coefficients
(`2`, `-3`, `-6`, ...) go through the generated coefficient constants
(`Grassmann.Kernel.Codegen.emitCoefs`). Checked against the reference by
`Tests.Codegen.Kernels` and `Tests.Codegen.Typed`.
-/
import Tests.Codegen.Common

namespace CodegenTests.Diag

grassmann_kernels D!"1,2,-3"

end CodegenTests.Diag
