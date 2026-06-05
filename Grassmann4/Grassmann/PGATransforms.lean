/-
  Grassmann/PGATransforms.lean - Packed PGA3 translation and rigid motors

  Extensions for the MV-backed PGA3 API that mirror dense constructors from
  `PGA.Proof`, while keeping user-facing Float operations on packed `MV`.
-/
import Grassmann.PGA

namespace Grassmann
namespace PGA

/-! ## Packed PGA3 Translators -/

/-- Create a packed PGA3 translator with displacement coefficients `(tx, ty, tz)`.

The coefficient layout mirrors `PGA.Proof.translator`:
`1 + tx/2 e01 + ty/2 e02 + tz/2 e03`.

The current `PGA3` signature is represented as `Cl(3, 1)`, so this constructor
tracks the dense reference semantics rather than proving true degenerate-PGA
Euclidean point-shift behavior. -/
@[inline]
def translator3 (tx ty tz : Float) : Motor PGA3 :=
  MV.one PGA3
    |>.setCoeff 9 (tx / 2.0)   -- e01
    |>.setCoeff 10 (ty / 2.0)  -- e02
    |>.setCoeff 12 (tz / 2.0)  -- e03

/-- Create a packed PGA3 rigid motor that rotates first, then translates.

This is the packed counterpart of `translator * rotor` in the dense API. -/
@[inline]
def rigidMotor3 (dx dy dz theta tx ty tz : Float) : Motor PGA3 :=
  Motor.compose (translator3 tx ty tz) (motor3 dx dy dz theta)

end PGA
end Grassmann
