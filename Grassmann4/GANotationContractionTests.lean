import Grassmann.GANotation

namespace Grassmann.GANotationContractionTests

private def sig : Signature 3 := Signature.euclidean 3

private def e1 : MultivectorS sig Float := MultivectorS.basis ⟨0, by omega⟩
private def e2 : MultivectorS sig Float := MultivectorS.basis ⟨1, by omega⟩
private def e3 : MultivectorS sig Float := MultivectorS.basis ⟨2, by omega⟩

private def sameCoeffs (a b : MultivectorS sig Float) : Bool :=
  (List.range 8).all fun mask => a.coeff mask == b.coeff mask

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"GANotation contraction regression: {label}"

def run : IO Unit := do
  let e12 := e1 * e2
  let e23 := e2 * e3

  -- These are the key regressions: the old notation implementation returned
  -- the geometric product (-e2, e123, and e12 respectively), not zero.
  require "higher-grade left operand must contract to zero"
    ((e12 ⌋ₛ e1).isZero)
  require "disjoint blades must left-contract to zero"
    ((e1 ⌋ₛ e23).isZero)
  require "lower-grade left operand must right-contract to zero"
    ((e1 ⌊ₛ e12).isZero)

  -- Positive and negative anchors ensure the notation preserves signs.
  require "e1 left-contract e12 = e2"
    ((e1 ⌋ₛ e12).coeff 2 == 1.0 && (e1 ⌋ₛ e12).nnz == 1)
  require "e2 left-contract e12 = -e1"
    ((e2 ⌋ₛ e12).coeff 1 == -1.0 && (e2 ⌋ₛ e12).nnz == 1)
  require "e12 right-contract e1 = e2"
    ((e12 ⌊ₛ e1).coeff 2 == 1.0 && (e12 ⌊ₛ e1).nnz == 1)
  require "e12 right-contract e2 = -e1"
    ((e12 ⌊ₛ e2).coeff 1 == -1.0 && (e12 ⌊ₛ e2).nnz == 1)

  -- A mixed-grade input catches accidental homogeneous-only shortcuts.
  let a := MultivectorS.scalar 2.0 + e1 + e12
  let b := MultivectorS.scalar (-3.0) + e2 + e23
  require "left notation delegates for mixed grades"
    (sameCoeffs (a ⌋ₛ b) (MultivectorS.leftContract a b))
  require "right notation delegates for mixed grades"
    (sameCoeffs (a ⌊ₛ b) (MultivectorS.rightContract a b))

  IO.println "GANotation contraction tests passed"

end Grassmann.GANotationContractionTests

def main : IO Unit := Grassmann.GANotationContractionTests.run
