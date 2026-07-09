import Grassmann.Multivector

namespace Grassmann.VersorInverseTests

private def sig : Signature 3 := Signature.euclidean 3

private def e1 : Multivector sig Float := Multivector.basis ⟨0, by omega⟩
private def e2 : Multivector sig Float := Multivector.basis ⟨1, by omega⟩

private def sameCoeffs (a b : Multivector sig Float) : Bool :=
  (List.finRange 8).all fun i => a.coeffs i == b.coeffs i

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"versor inverse regression: {label}"

def run : IO Unit := do
  let one : Multivector sig Float := Multivector.one
  let zero : Multivector sig Float := Multivector.zero
  let e12 := e1 * e2

  -- (1 + e12)(1 - e12) = 2, so this is a valid, non-unit versor.
  let versor := one + e12
  let reverseProduct := versor * versor†
  require "valid reverse product is recognized as scalar"
    reverseProduct.isScalarExact
  require "valid reverse product has scalar value two"
    (reverseProduct.scalarPart == 2.0)
  match versor.versorInv? with
  | none => require "valid versor must be accepted" false
  | some inverse =>
      require "checked result is a right inverse"
        (sameCoeffs (versor * inverse) one)
      require "checked result is a left inverse"
        (sameCoeffs (inverse * versor) one)
      require "checked result is reverse divided by two"
        (sameCoeffs inverse (versor†.smul 0.5))

  -- This is the concrete old bug: (1 + e1)(1 + e1)
  -- = 2 + 2e1. Its scalar part is nonzero, but it is not a scalar product.
  let nonVersor := one + e1
  let nonScalarProduct := nonVersor * nonVersor†
  require "counterexample keeps a non-scalar coefficient"
    (nonScalarProduct.coeffs ⟨1, by omega⟩ == 2.0)
  require "counterexample is not classified as scalar"
    (!nonScalarProduct.isScalarExact)
  require "checked inverse rejects non-scalar reverse product"
    nonVersor.versorInv?.isNone

  require "checked inverse rejects zero scalar reverse product"
    zero.versorInv?.isNone

  IO.println "checked versor inverse tests passed"

end Grassmann.VersorInverseTests

def main : IO Unit := Grassmann.VersorInverseTests.run
