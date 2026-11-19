/-
  Grassmann/CABI.lean — Strictly Init-only exported C ABI leaf module

  This module is the sole Lean-facing FFI export boundary for:
  1. Direct packed `double*` numeric GA kernels (STA `Cl(3,1)` `-+++`, R3 +
     exact rational rotor, PGA2, PGA3 full & 8-float motors, CGA2, CGA3, and
     generic `Cl(p, q, r)` up to 64 blades) — zero JSON / string roundtrip!
  2. Canonical `SceneIR` v1 (`GSIR`) stateful Studio session API
     (`grassmann_studio_{create,destroy,dispatch_bin,dispatch_json,get_frame}`).

  Transitive imports are strictly `Init`-only (ZERO `Lean.*`, `Lake.*`, or `Std.*`)
  so standalone macOS/visionOS dylibs link to ~2–5 MB (instead of 182–264 MB) and
  compile cleanly to WebAssembly via `lean -c` + `emcc`.

  Public callers include `include/grassmann/cabi.h` (never `<lean/lean.h>`).
-/
import Grassmann.CABI.Kernels
import Grassmann.CABI.Studio

namespace Grassmann.CABI

open Grassmann.CABI.Kernels
open Grassmann.CABI.Studio

/-! ### Generic `Cl(p, q, r)` Exports -/

@[export grassmann_lean_cl_mul]
def clMulExport (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  clMul p q r a b

@[export grassmann_lean_cl_wedge]
def clWedgeExport (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  clWedge p q r a b

@[export grassmann_lean_cl_join]
def clJoinExport (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  clJoin p q r a b

@[export grassmann_lean_cl_left_contract]
def clLeftContractExport (p q r : UInt32) (a b : FloatArray) : FloatArray :=
  clLeftContract p q r a b

@[export grassmann_lean_cl_reverse]
def clReverseExport (p q r : UInt32) (a : FloatArray) : FloatArray :=
  clReverse p q r a

@[export grassmann_lean_cl_dual]
def clDualExport (p q r : UInt32) (a : FloatArray) : FloatArray :=
  clDual p q r a

@[export grassmann_lean_cl_sandwich]
def clSandwichExport (p q r : UInt32) (versor x : FloatArray) : FloatArray :=
  clSandwich p q r versor x

/-! ### STA `Cl(3, 1)` (`-+++`) Exports -/

@[export grassmann_lean_sta_mul]
def staMulExport (a b : FloatArray) : FloatArray := staMul a b

@[export grassmann_lean_sta_wedge]
def staWedgeExport (a b : FloatArray) : FloatArray := staWedge a b

@[export grassmann_lean_sta_left_contract]
def staLeftContractExport (a b : FloatArray) : FloatArray := staLeftContract a b

@[export grassmann_lean_sta_reverse]
def staReverseExport (a : FloatArray) : FloatArray := staReverse a

@[export grassmann_lean_sta_boost_rotor]
def staBoostRotorExport (phi ux uy uz : Float) : FloatArray :=
  staBoostRotor phi ux uy uz

@[export grassmann_lean_sta_sandwich]
def staSandwichExport (r x : FloatArray) : FloatArray := staSandwich r x

@[export grassmann_lean_sta_spatial_wedge]
def staSpatialWedgeExport (a b : FloatArray) : FloatArray := staSpatialWedge a b

/-! ### R3 `Cl(3, 0, 0)` + Exact Rational Rotor Exports -/

@[export grassmann_lean_r3_mul]
def r3MulExport (a b : FloatArray) : FloatArray := r3Mul a b

@[export grassmann_lean_r3_wedge]
def r3WedgeExport (a b : FloatArray) : FloatArray := r3Wedge a b

@[export grassmann_lean_r3_reverse]
def r3ReverseExport (a : FloatArray) : FloatArray := r3Reverse a

@[export grassmann_lean_r3_sandwich]
def r3SandwichExport (r x : FloatArray) : FloatArray := r3Sandwich r x

@[export grassmann_lean_r3_apply_rational_rotor]
def r3ApplyRationalRotorExport (s b12 b13 b23 x y z : Float) : FloatArray :=
  r3ApplyRationalRotor s b12 b13 b23 x y z

@[export grassmann_lean_r3_rational_rotor_cayley]
def r3RationalRotorCayleyExport (t1 t2 t3 : Float) : FloatArray :=
  r3RationalRotorFromCayley t1 t2 t3

/-! ### PGA2 `Cl(2, 0, 1)` Exports -/

@[export grassmann_lean_pga2_mul]
def pga2MulExport (a b : FloatArray) : FloatArray := pga2Mul a b

@[export grassmann_lean_pga2_meet]
def pga2MeetExport (a b : FloatArray) : FloatArray := pga2Meet a b

@[export grassmann_lean_pga2_join]
def pga2JoinExport (a b : FloatArray) : FloatArray := pga2Join a b

@[export grassmann_lean_pga2_left_contract]
def pga2LeftContractExport (a b : FloatArray) : FloatArray := pga2LeftContract a b

@[export grassmann_lean_pga2_reverse]
def pga2ReverseExport (a : FloatArray) : FloatArray := pga2Reverse a

@[export grassmann_lean_pga2_point]
def pga2PointExport (x y : Float) : FloatArray := pga2Point x y

@[export grassmann_lean_pga2_line]
def pga2LineExport (a b c : Float) : FloatArray := pga2Line a b c

@[export grassmann_lean_pga2_sandwich]
def pga2SandwichExport (r x : FloatArray) : FloatArray := pga2Sandwich r x

/-! ### PGA3 `Cl(3, 0, 1)` Full & Specialized 8-Float Motor Exports -/

@[export grassmann_lean_pga3_mul]
def pga3MulExport (a b : FloatArray) : FloatArray := pga3Mul a b

@[export grassmann_lean_pga3_meet]
def pga3MeetExport (a b : FloatArray) : FloatArray := pga3Meet a b

@[export grassmann_lean_pga3_join]
def pga3JoinExport (a b : FloatArray) : FloatArray := pga3Join a b

@[export grassmann_lean_pga3_left_contract]
def pga3LeftContractExport (a b : FloatArray) : FloatArray := pga3LeftContract a b

@[export grassmann_lean_pga3_reverse]
def pga3ReverseExport (a : FloatArray) : FloatArray := pga3Reverse a

@[export grassmann_lean_pga3_make_rotor]
def pga3MakeRotorExport (ax ay az angle : Float) : FloatArray :=
  pga3MakeRotor ax ay az angle

@[export grassmann_lean_pga3_make_translator]
def pga3MakeTranslatorExport (tx ty tz : Float) : FloatArray :=
  pga3MakeTranslator tx ty tz

@[export grassmann_lean_pga3_motor_compose]
def pga3MotorComposeExport (a b : FloatArray) : FloatArray := pga3MotorCompose a b

@[export grassmann_lean_pga3_motor_reverse]
def pga3MotorReverseExport (m : FloatArray) : FloatArray := pga3MotorReverse m

@[export grassmann_lean_pga3_motor_is_unit]
def pga3MotorIsUnitExport (m : FloatArray) (tol : Float) : Bool := pga3MotorIsUnit m tol

@[export grassmann_lean_pga3_motor_normalize]
def pga3MotorNormalizeExport (m : FloatArray) : FloatArray := pga3MotorNormalize m

@[export grassmann_lean_pga3_motor_inverse]
def pga3MotorInverseExport (m : FloatArray) : FloatArray := pga3MotorInverse m

@[export grassmann_lean_pga3_motor_exp]
def pga3MotorExpExport (b01 b02 b03 b12 b13 b23 : Float) : FloatArray :=
  pga3MotorExp b01 b02 b03 b12 b13 b23

@[export grassmann_lean_pga3_motor_log]
def pga3MotorLogExport (m : FloatArray) : FloatArray := pga3MotorLog m

@[export grassmann_lean_pga3_motor_slerp]
def pga3MotorSlerpExport (m0 m1 : FloatArray) (t : Float) : FloatArray :=
  pga3MotorSlerp m0 m1 t

@[export grassmann_lean_pga3_motor_to_mat4]
def pga3MotorToMat4Export (m : FloatArray) : FloatArray := pga3MotorToMat4 m

@[export grassmann_lean_pga3_motor_apply_xyz]
def pga3MotorApplyXYZExport (m : FloatArray) (x y z : Float) : FloatArray :=
  pga3MotorApplyXYZ m x y z

@[export grassmann_lean_pga3_motor_apply_xyz_batch]
def pga3MotorApplyXYZBatchExport (m xyz : FloatArray) : FloatArray :=
  pga3MotorApplyXYZBatch m xyz

/-! ### CGA2 `Cl(3, 1)` & CGA3 `Cl(4, 1)` Exports -/

@[export grassmann_lean_cga2_mul]
def cga2MulExport (a b : FloatArray) : FloatArray := cga2Mul a b

@[export grassmann_lean_cga2_wedge]
def cga2WedgeExport (a b : FloatArray) : FloatArray := cga2Wedge a b

@[export grassmann_lean_cga2_up]
def cga2UpExport (x y : Float) : FloatArray := cga2Up x y

@[export grassmann_lean_cga3_mul]
def cga3MulExport (a b : FloatArray) : FloatArray := cga3Mul a b

@[export grassmann_lean_cga3_wedge]
def cga3WedgeExport (a b : FloatArray) : FloatArray := cga3Wedge a b

@[export grassmann_lean_cga3_left_contract]
def cga3LeftContractExport (a b : FloatArray) : FloatArray := cga3LeftContract a b

@[export grassmann_lean_cga3_reverse]
def cga3ReverseExport (a : FloatArray) : FloatArray := cga3Reverse a

@[export grassmann_lean_cga3_sandwich]
def cga3SandwichExport (r x : FloatArray) : FloatArray := cga3Sandwich r x

@[export grassmann_lean_cga3_up]
def cga3UpExport (x y z : Float) : FloatArray := cga3Up x y z

@[export grassmann_lean_cga3_down]
def cga3DownExport (p : FloatArray) : FloatArray := cga3Down p

@[export grassmann_lean_cga3_dual_sphere]
def cga3DualSphereExport (cx cy cz r : Float) : FloatArray := cga3DualSphere cx cy cz r

@[export grassmann_lean_cga3_dual_plane]
def cga3DualPlaneExport (nx ny nz d : Float) : FloatArray := cga3DualPlane nx ny nz d

/-! ### Canonical `SceneIR` v1 (`GSIR`) Studio Session Exports -/

@[export grassmann_lean_studio_create]
def studioCreateExport : IO UInt64 := createSession

@[export grassmann_lean_studio_destroy]
def studioDestroyExport (sid : UInt64) : IO Unit := destroySession sid

@[export grassmann_lean_studio_dispatch_bin]
def studioDispatchBinExport (sid : UInt64) (eventBuf : ByteArray) : IO (Int32 × ByteArray) :=
  dispatchBin sid eventBuf

@[export grassmann_lean_studio_dispatch_json]
def studioDispatchJsonExport (sid : UInt64) (eventJson : String) : IO (Int32 × ByteArray) :=
  dispatchJson sid eventJson

@[export grassmann_lean_studio_get_frame]
def studioGetFrameExport (sid : UInt64) : IO (Int32 × ByteArray) :=
  getCachedFrame sid

@[export grassmann_lean_studio_preset_catalog]
def studioPresetCatalogExport (_ : UInt8) : ByteArray :=
  getPresetCatalogJson.toUTF8

end Grassmann.CABI
