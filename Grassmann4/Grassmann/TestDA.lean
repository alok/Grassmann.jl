import Grassmann.DataArray

/-! ### Quick test of SciLean-backed DataArray types -/

namespace Grassmann.TestDA

open Grassmann

-- Test GrassmannArray types
#check GrassmannArray
#check (GrassmannArray 3 : Type)
#check GrassmannArray.zeros 3
#check GrassmannArray.scalar 3 1.0

-- Test EvenArray types  
#check EvenArray
#check (EvenArray 3 : Type)
#check EvenArray.zeros 3

-- Test legacy DataArray
#check DataArray
#check DataArray.zeros 16

-- Verify type equalities
example : GrassmannArray 3 = SciLean.DataArrayN Float (SciLean.Idx (2^3)) := rfl
example : EvenArray 3 = SciLean.DataArrayN Float (SciLean.Idx (2^(3-1))) := rfl
example : DataArray = SciLean.DataArray Float := rfl

#print "TestDA types verified!"

end Grassmann.TestDA
