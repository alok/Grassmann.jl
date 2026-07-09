import Grassmann.Products

namespace Grassmann.ProductsCorrectnessTests

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"Products regression: {label}"

private def sameSpaceInterop
    (op : BladeProduct R3 → BladeProduct R3 → BladeProduct R3)
    (a b : Blade R3) : BladeProduct R3 :=
  Interop.interop op a b

def run : IO Unit := do
  -- Same-space interop must inject each operand as a unit signed blade. The old
  -- implementation squared both inputs, turning e1 and e2 into scalar +1.
  let left := sameSpaceInterop (fun a _ => a) e1 e2
  let right := sameSpaceInterop (fun _ b => b) e1 e2
  require "interop preserves the left blade"
    (decide (left = BladeProduct.nonzero 1 (e1 : Blade R3)))
  require "interop preserves the right blade"
    (decide (right = BladeProduct.nonzero 1 (e2 : Blade R3)))

  -- Vector reverse has sign +1, so the established vector behavior remains.
  require "vector sandwich keeps its reverse sign"
    (decide (sandwichBlades (e1 : Blade R3) (e2 : Blade R3) =
      BladeProduct.nonzero (-1) (e2 : Blade R3)))

  -- Bivector and trivector reverse signs are -1. These two cases failed before
  -- the grade-dependent reverse factor was included in the final coefficient.
  require "bivector sandwich includes reverse sign"
    (decide (sandwichBlades (e12 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero (-1) (e1 : Blade R3)))
  require "bivector sandwich fixes the orthogonal axis"
    (decide (sandwichBlades (e12 : Blade R3) (e3 : Blade R3) =
      BladeProduct.nonzero 1 (e3 : Blade R3)))
  require "trivector sandwich includes reverse sign"
    (decide (sandwichBlades (e123 : Blade R3) (e1 : Blade R3) =
      BladeProduct.nonzero 1 (e1 : Blade R3)))

  IO.println "Products correctness tests passed"

end Grassmann.ProductsCorrectnessTests

def main : IO Unit := Grassmann.ProductsCorrectnessTests.run
