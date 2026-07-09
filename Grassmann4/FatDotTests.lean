import Grassmann.MVDense
import Grassmann.SparseMultivector

namespace Grassmann.FatDotTests

private def sig : Signature 3 := Signature.euclidean 3

private def denseE1 : Multivector sig Float := Multivector.basis ⟨0, by omega⟩
private def denseE2 : Multivector sig Float := Multivector.basis ⟨1, by omega⟩

private def sparseE1 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
private def sparseE2 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩

private def sameDense (a b : Multivector sig Float) : Bool :=
  (List.finRange 8).all fun i => a.coeffs i == b.coeffs i

private def sparseMatchesDense
    (sparse : MultivectorS sig Float) (dense : Multivector sig Float) : Bool :=
  (List.range 8).all fun mask =>
    if h : mask < 8 then sparse.coeff mask == dense.coeffs ⟨mask, h⟩ else true

private def packedMatchesDense
    (packed : MV sig .full) (dense : Multivector sig Float) : Bool :=
  sameDense packed.toMultivector dense

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"fat-dot regression: {label}"

def run : IO Unit := do
  let denseScalar2 : Multivector sig Float := Multivector.scalar 2.0
  let denseScalar3 : Multivector sig Float := Multivector.scalar 3.0
  let sparseScalar2 : MultivectorS sig Float := MultivectorS.scalar 2.0
  let sparseScalar3 : MultivectorS sig Float := MultivectorS.scalar 3.0
  let packedScalar2 : MV sig .full := MV.ofMultivector denseScalar2 .full
  let packedScalar3 : MV sig .full := MV.ofMultivector denseScalar3 .full
  let denseScalarResult := Multivector.fatDot denseScalar2 denseScalar3
  require "dense scalars are not counted twice"
    (sameDense denseScalarResult (Multivector.scalar 6.0))
  require "sparse scalars are not counted twice"
    (sparseMatchesDense (MultivectorS.fatDot sparseScalar2 sparseScalar3)
      (Multivector.scalar 6.0))
  require "packed scalars are not counted twice"
    (packedMatchesDense (MV.fatDot packedScalar2 packedScalar3)
      (Multivector.scalar 6.0))
  let denseE12 := denseE1 * denseE2
  let sparseE12 := sparseE1 * sparseE2
  let packedE12 : MV sig .full := MV.ofMultivector denseE12 .full
  -- Grassmann contraction reverses the lower-grade operand.  In particular,
  -- the bivector norm is +1; the Hestenes grade-difference product is -1.
  let expectedNorm : Multivector sig Float := Multivector.scalar 1.0
  require "dense bivector fat dot uses the Grassmann reverse convention"
    (sameDense (Multivector.fatDot denseE12 denseE12) expectedNorm)
  require "sparse bivector fat dot uses the Grassmann reverse convention"
    (sparseMatchesDense (MultivectorS.fatDot sparseE12 sparseE12) expectedNorm)
  require "packed bivector fat dot uses the Grassmann reverse convention"
    (packedMatchesDense (MV.fatDot packedE12 packedE12) expectedNorm)
  require "Hestenes inner product remains a distinct operation"
    ((MultivectorS.innerProduct sparseE12 sparseE12).scalarPart == -1.0)
  -- Julia's ⊙ is symmetrization, not contraction.  For e12 the two operations
  -- have opposite scalar signs, which prevents the notation from drifting back.
  require "sparse ⊙ notation is symmetrization"
    (sparseMatchesDense (sparseE12 ⊙ₛ sparseE12) (Multivector.scalar (-1.0)))
  let denseA := denseScalar2 + denseE1 + denseE12
  let denseB := Multivector.scalar (-3.0) + denseE2 + (denseE2 * denseE1)
  let sparseA := sparseScalar2 + sparseE1 + sparseE12
  let sparseB := MultivectorS.scalar (-3.0) + sparseE2 + (sparseE2 * sparseE1)
  let packedA : MV sig .full := MV.ofMultivector denseA .full
  let packedB : MV sig .full := MV.ofMultivector denseB .full
  let denseMixed := Multivector.fatDot denseA denseB
  require "sparse mixed-grade fat dot matches dense"
    (sparseMatchesDense (MultivectorS.fatDot sparseA sparseB) denseMixed)
  require "packed mixed-grade fat dot matches dense"
    (packedMatchesDense (MV.fatDot packedA packedB) denseMixed)
  IO.println "fat-dot tests passed"

end Grassmann.FatDotTests

def main : IO Unit := Grassmann.FatDotTests.run
