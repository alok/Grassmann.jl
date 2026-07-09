import Grassmann.DataArray

/-! ### Quick test of built-in FloatArray-backed DataArray types -/

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

-- Verify the public aliases use Lean's contiguous unboxed FloatArray.
example : GrassmannArray 3 = FloatArray := rfl
example : EvenArray 3 = FloatArray := rfl
example : DataArray = FloatArray := rfl

example : (GrassmannArray.zeros 3).size = 8 := by native_decide
example : (EvenArray.zeros 3).size = 4 := by native_decide
example : (GrassmannArray.scalar 3 2.5).get! 0 == 2.5 := by native_decide

#print "TestDA types verified!"

end Grassmann.TestDA
