import Grassmann.Forms.Mat
import Grassmann.Forms.Operator
import Grassmann.Forms.Compound
import Grassmann.Forms.Outermorphism
import Grassmann.Forms.Diagonal

/-!
# Grassmann.Forms: linear algebra of Grassmann elements

Port of Grassmann.jl `src/forms.jl` (and the determinant/simplex part of
`src/composite.jl`); port-notes/grassmann-forms.md.

## Map

* `Grassmann.Forms.Mat`: dense column-major matrices over packed coefficients
  (a `FloatArray` at `Float`), with Julia-order multiply-accumulate loops.
* `Grassmann.Forms.Operator`: `TensorOperator V ld W lc α` (Julia
  `TensorOperator{V,W,<:ld{V,<:lc{W}}}`), `Endomorphism`, `Simplex`; application
  `T x`, `T * x`, `T ⋅ x`, row application `x ⋅ T`, composition, transpose,
  trace, diagonal, uniform scalings, bilinear forms, `bivector`, `companion`.
* `Grassmann.Forms.Compound`: compounds `Λᵍ T`, `∧(T)`, `det`, the Cramer
  adjugate/cofactor/inverse/solve, pseudo-inverses.
* `Grassmann.Forms.Outermorphism`: `Outermorphism V W α`, the compounds of a
  grade-1 map acting on every grade, `Spinor`, `CoSpinor` and `Multivector`.
* `Grassmann.Forms.Diagonal`: `DiagonalOperator V l α`, `DiagonalMorphism`,
  `DiagonalOutermorphism`.
-/
