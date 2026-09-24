/**
 * GrassmannPGA.h - C/C++ FFI header for Grassmann PGA operations
 *
 * This header exposes Lean 4 Clifford algebra computations to C/C++.
 * All functions work with raw float arrays representing multivectors.
 *
 * PGA3 (Projective Geometric Algebra) uses 16 coefficients for Cl(3,0,1):
 *   Index 0:  scalar (1)
 *   Index 1:  e0
 *   Index 2:  e1
 *   Index 3:  e12
 *   Index 4:  e2
 *   Index 5:  e31 (note: e31 = -e13)
 *   Index 6:  e23
 *   Index 7:  e123
 *   Index 8:  e3
 *   Index 9:  e01
 *   Index 10: e02
 *   Index 11: e012
 *   Index 12: e03
 *   Index 13: e031
 *   Index 14: e023
 *   Index 15: e0123 (pseudoscalar)
 *
 * For Unreal Engine integration:
 *   FVector(x,y,z) <-> PGA Point: e123 + x*e023 + y*e031 + z*e012
 *   FQuat(x,y,z,w) <-> PGA Rotor: w + x*e23 + y*e31 + z*e12
 *   FTransform     <-> PGA Motor: Rotor + Translator
 */

#ifndef GRASSMANN_PGA_H
#define GRASSMANN_PGA_H

#ifdef __cplusplus
extern "C" {
#endif

#include <lean/lean.h>

/* ============================================================================
 * Lean Runtime Initialization (call once at startup)
 * ============================================================================ */

/**
 * Initialize the Lean runtime. Must be called before any other functions.
 * Returns 0 on success, non-zero on failure.
 */
int grassmann_init(void);

/**
 * Shutdown the Lean runtime. Call when done using the library.
 */
void grassmann_shutdown(void);

/* ============================================================================
 * Helper functions for FloatArray handling
 * ============================================================================ */

/**
 * Create a FloatArray wrapper from a raw float pointer.
 * Caller is responsible for memory management.
 */
static inline lean_object* floats_to_lean(const float* data, size_t count) {
    lean_object* arr = lean_mk_empty_array_with_capacity(lean_unsigned_to_nat((unsigned)count));
    for (size_t i = 0; i < count; i++) {
        arr = lean_array_push(arr, lean_box_float((double)data[i]));
    }
    return lean_float_array_mk(arr);
}

/**
 * Extract floats from a Lean FloatArray result.
 * Returns number of elements written to output buffer.
 */
static inline size_t lean_to_floats(lean_object* arr, float* out, size_t max_count) {
    lean_object* data = lean_float_array_data(arr);
    size_t sz = lean_array_size(data);
    size_t count = sz < max_count ? sz : max_count;
    for (size_t i = 0; i < count; i++) {
        lean_object* elem = lean_array_get_core(data, i);
        out[i] = (float)lean_unbox_float(elem);
    }
    return count;
}

/* ============================================================================
 * PGA Point Operations
 * ============================================================================ */

/**
 * Create a PGA3 point from x,y,z coordinates.
 * Returns a FloatArray with 16 coefficients.
 * Point = e123 + x*e023 + y*e031 + z*e012
 */
LEAN_EXPORT lean_object* grassmann_pga_point(double x, double y, double z);

/**
 * Extract x,y,z from a PGA point.
 * Input: 16-float PGA point
 * Returns: FloatArray with 3 floats [x, y, z]
 */
LEAN_EXPORT lean_object* grassmann_pga_extract_point(lean_object* coeffs);

/* ============================================================================
 * PGA Motor Operations (Rotors + Translators)
 * ============================================================================ */

/**
 * Create a rotation motor (rotor) from axis and angle.
 * @param dx, dy, dz: Normalized axis of rotation
 * @param theta: Angle in radians
 * Returns: FloatArray with 16 coefficients
 * Rotor = cos(θ/2) + sin(θ/2)(dx*e23 + dy*e31 + dz*e12)
 */
LEAN_EXPORT lean_object* grassmann_pga_rotor(double dx, double dy, double dz, double theta);

/**
 * Create a translation motor.
 * @param tx, ty, tz: Translation vector
 * Returns: FloatArray with 16 coefficients
 * Translator = 1 + (tx/2)*e01 + (ty/2)*e02 + (tz/2)*e03
 */
LEAN_EXPORT lean_object* grassmann_pga_translator(double tx, double ty, double tz);

/**
 * Compose two motors: M1 * M2.
 * Use for combining transformations.
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_compose(lean_object* m1, lean_object* m2);

/**
 * Reverse (conjugate) of a motor: M†.
 * For normalized rotors, M† = M^(-1).
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_reverse(lean_object* m);

/**
 * Apply motor to point: M * P * M†.
 * This is the sandwich product that transforms points.
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_apply_point(lean_object* motor, lean_object* point);

/* ============================================================================
 * Unreal Engine Conversions
 * ============================================================================ */

/**
 * Extract quaternion (x,y,z,w) from PGA motor for FQuat.
 * Returns: FloatArray with 4 floats [qx, qy, qz, qw]
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_to_quat(lean_object* motor);

/**
 * Extract translation (x,y,z) from PGA motor for FVector.
 * Returns: FloatArray with 3 floats [tx, ty, tz]
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_to_translation(lean_object* motor);

/**
 * Create PGA motor from UE FQuat and FVector.
 * @param qx, qy, qz, qw: Quaternion components (FQuat)
 * @param tx, ty, tz: Translation (FVector)
 * Returns: FloatArray with 16 coefficients
 */
LEAN_EXPORT lean_object* grassmann_pga_motor_from_ue(
    double qx, double qy, double qz, double qw,
    double tx, double ty, double tz);

/* ============================================================================
 * Utility Operations
 * ============================================================================ */

/**
 * Euclidean distance squared between two points.
 * Returns: double (not a FloatArray)
 */
LEAN_EXPORT double grassmann_pga_distance_sq(
    double x1, double y1, double z1,
    double x2, double y2, double z2);

/**
 * Quaternion spherical linear interpolation (SLERP).
 * @param q1x..q1w: First quaternion
 * @param q2x..q2w: Second quaternion
 * @param t: Interpolation parameter [0,1]
 * Returns: FloatArray with 4 floats [qx, qy, qz, qw]
 */
LEAN_EXPORT lean_object* grassmann_quat_slerp(
    double q1x, double q1y, double q1z, double q1w,
    double q2x, double q2y, double q2z, double q2w,
    double t);

#ifdef __cplusplus
}
#endif

#endif /* GRASSMANN_PGA_H */
