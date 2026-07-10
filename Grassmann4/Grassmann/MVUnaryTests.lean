/-
  Grassmann/MVUnaryTests.lean - Focused packed unary-operation regressions

  These compile-time checks pin packed index decoding and the exact unary
  layouts used by reverse, involution, conjugation, and projections.
-/
import Grassmann.MVDense

namespace Grassmann.MVUnaryTests

set_option linter.hashCommand false

/-! ## Full-storage index identity -/

/- Every valid full packed index is already its blade mask. -/
#guard
  (List.range 7).all fun n =>
    (List.range (2 ^ n)).all fun i =>
      MV.unpackIdx n .full i == i && MV.packIdx n .full i == i

end Grassmann.MVUnaryTests
