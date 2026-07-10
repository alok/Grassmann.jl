#include <lean/lean.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define GRASSMANN_CABI_BUILD 1
#include "grassmann/cabi.h"

/* These runtime entry points are exported by Lean but not declared by lean.h. */
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

/* Generated module initializer for Grassmann/CABI.lean. */
extern lean_obj_res initialize_Grassmann_Grassmann_CABI(uint8_t builtin);

/* Private Lean-object ABI. Only this shim may call these functions. */
extern lean_obj_res grassmann_lean_pga3_make_point_v1(double, double, double);
extern lean_obj_res grassmann_lean_pga3_make_rotor_v1(
  double, double, double, double);
extern lean_obj_res grassmann_lean_pga3_make_translator_v1(
  double, double, double);
extern lean_obj_res grassmann_lean_pga3_motor_compose_v1(
  lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_reverse_v1(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_apply_point_v1(
  lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_extract_point_v1(lean_obj_arg);
extern uint8_t grassmann_pga3_motor_is_unit_impl_v1(lean_obj_arg, double);
extern lean_obj_res grassmann_pga3_motor_normalize_impl_v1(lean_obj_arg);
extern lean_obj_res grassmann_pga3_motor_inverse_impl_v1(lean_obj_arg);
extern lean_obj_res grassmann_pga3_motor_apply_xyz_batch_impl_v1(
  lean_obj_arg, lean_obj_arg);

/* 0 = not initialized, 1 = initialized, -1 = permanently failed. */
static int grassmann_runtime_state = 0;

static grassmann_status_v1 require_runtime(void) {
  return grassmann_runtime_state == 1
    ? GRASSMANN_OK_V1
    : GRASSMANN_NOT_INITIALIZED_V1;
}

/* Allocate a native, unboxed Lean FloatArray and copy caller-owned doubles. */
static lean_obj_res packed_array(const double *src, size_t count) {
  lean_obj_res out = lean_alloc_sarray(sizeof(double), count, count);
  if (count != 0) {
    memcpy(lean_float_array_cptr(out), src, count * sizeof(double));
  }
  return out;
}

/* Validate, copy, and release an owned FloatArray result. */
static grassmann_status_v1 copy_result(
    lean_obj_res result,
    double *dst,
    size_t expected) {
  if (result == NULL || !lean_is_sarray(result) ||
      lean_sarray_elem_size(result) != sizeof(double) ||
      lean_sarray_size(result) != expected) {
    if (result != NULL) {
      lean_dec(result);
    }
    return GRASSMANN_BAD_RESULT_V1;
  }

  if (expected != 0) {
    memcpy(dst, lean_float_array_cptr(result), expected * sizeof(double));
  }
  lean_dec(result);
  return GRASSMANN_OK_V1;
}

static int motor_coefficients_are_finite(
    const grassmann_pga3_motor_v1 *motor) {
  for (size_t i = 0; i < 8; ++i) {
    if (!isfinite(motor->coeff[i])) {
      return 0;
    }
  }
  return 1;
}

static void motor_invariants(
    const grassmann_pga3_motor_v1 *motor,
    double *rotor_norm_sq,
    double *twice_study) {
  const double *a = motor->coeff;
  *rotor_norm_sq =
    a[0] * a[0] + a[1] * a[1] + a[2] * a[2] + a[3] * a[3];
  *twice_study = 2.0 * (
    a[0] * a[7] - a[1] * a[6] + a[2] * a[5] - a[3] * a[4]);
}

static int motor_is_valid(
    const grassmann_pga3_motor_v1 *motor,
    double tolerance) {
  double rotor_norm_sq;
  double twice_study;
  if (!motor_coefficients_are_finite(motor)) {
    return 0;
  }
  motor_invariants(motor, &rotor_norm_sq, &twice_study);
  return isfinite(rotor_norm_sq) &&
    isfinite(twice_study) &&
    rotor_norm_sq > tolerance &&
    isfinite(1.0 / rotor_norm_sq) &&
    fabs(twice_study) <= tolerance * rotor_norm_sq;
}

uint32_t grassmann_cabi_version_v1(void) {
  return GRASSMANN_CABI_VERSION_V1;
}

grassmann_status_v1 grassmann_initialize_v1(void) {
  if (grassmann_runtime_state == 1) {
    return GRASSMANN_OK_V1;
  }
  if (grassmann_runtime_state < 0) {
    return GRASSMANN_INIT_FAILED_V1;
  }

  lean_initialize_runtime_module();
  lean_obj_res result = initialize_Grassmann_Grassmann_CABI(1);
  if (!lean_io_result_is_ok(result)) {
    lean_io_result_show_error(result);
    lean_dec(result);
    grassmann_runtime_state = -1;
    return GRASSMANN_INIT_FAILED_V1;
  }

  lean_dec_ref(result);
  lean_io_mark_end_initialization();
  grassmann_runtime_state = 1;
  return GRASSMANN_OK_V1;
}

grassmann_status_v1 grassmann_thread_initialize_v1(void) {
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_initialize_thread();
  return GRASSMANN_OK_V1;
}

grassmann_status_v1 grassmann_thread_finalize_v1(void) {
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_finalize_thread();
  return GRASSMANN_OK_V1;
}

grassmann_status_v1 grassmann_pga3_make_point_v1(
    double x,
    double y,
    double z,
    grassmann_pga3_point_v1 *out) {
  if (out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  return copy_result(
    grassmann_lean_pga3_make_point_v1(x, y, z), out->coeff, 8);
}

grassmann_status_v1 grassmann_pga3_extract_point_v1(
    const grassmann_pga3_point_v1 *point,
    double out_xyz[3]) {
  if (point == NULL || out_xyz == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_obj_res input = packed_array(point->coeff, 8);
  /* Exported Lean functions consume their object arguments. */
  return copy_result(
    grassmann_lean_pga3_extract_point_v1(input), out_xyz, 3);
}

grassmann_status_v1 grassmann_pga3_make_rotor_v1(
    double axis_x,
    double axis_y,
    double axis_z,
    double angle,
    grassmann_pga3_motor_v1 *out) {
  if (out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  return copy_result(
    grassmann_lean_pga3_make_rotor_v1(axis_x, axis_y, axis_z, angle),
    out->coeff,
    8);
}

grassmann_status_v1 grassmann_pga3_make_translator_v1(
    double x,
    double y,
    double z,
    grassmann_pga3_motor_v1 *out) {
  if (out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  return copy_result(
    grassmann_lean_pga3_make_translator_v1(x, y, z), out->coeff, 8);
}

grassmann_status_v1 grassmann_pga3_motor_compose_v1(
    const grassmann_pga3_motor_v1 *after,
    const grassmann_pga3_motor_v1 *before,
    grassmann_pga3_motor_v1 *out) {
  if (after == NULL || before == NULL || out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_obj_res after_array = packed_array(after->coeff, 8);
  lean_obj_res before_array = packed_array(before->coeff, 8);
  return copy_result(
    grassmann_lean_pga3_motor_compose_v1(after_array, before_array),
    out->coeff,
    8);
}

grassmann_status_v1 grassmann_pga3_motor_reverse_v1(
    const grassmann_pga3_motor_v1 *motor,
    grassmann_pga3_motor_v1 *out) {
  if (motor == NULL || out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_obj_res input = packed_array(motor->coeff, 8);
  return copy_result(
    grassmann_lean_pga3_motor_reverse_v1(input), out->coeff, 8);
}

grassmann_status_v1 grassmann_pga3_motor_apply_point_v1(
    const grassmann_pga3_motor_v1 *motor,
    const grassmann_pga3_point_v1 *point,
    grassmann_pga3_point_v1 *out) {
  if (motor == NULL || point == NULL || out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  lean_obj_res motor_array = packed_array(motor->coeff, 8);
  lean_obj_res point_array = packed_array(point->coeff, 8);
  return copy_result(
    grassmann_lean_pga3_motor_apply_point_v1(motor_array, point_array),
    out->coeff,
    8);
}

grassmann_status_v1 grassmann_pga3_motor_is_unit_v1(
    const grassmann_pga3_motor_v1 *motor,
    double tolerance,
    int *out_is_unit) {
  if (motor == NULL || out_is_unit == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  if (!isfinite(tolerance) || tolerance < 0.0 ||
      !motor_coefficients_are_finite(motor)) {
    *out_is_unit = 0;
    return GRASSMANN_OK_V1;
  }
  lean_obj_res input = packed_array(motor->coeff, 8);
  *out_is_unit =
    grassmann_pga3_motor_is_unit_impl_v1(input, tolerance) != 0 ? 1 : 0;
  return GRASSMANN_OK_V1;
}

grassmann_status_v1 grassmann_pga3_motor_normalize_v1(
    const grassmann_pga3_motor_v1 *motor,
    grassmann_pga3_motor_v1 *out) {
  if (motor == NULL || out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  if (!motor_is_valid(
        motor, GRASSMANN_PGA3_MOTOR_VALIDITY_TOLERANCE_V1)) {
    return GRASSMANN_INVALID_MOTOR_V1;
  }
  lean_obj_res input = packed_array(motor->coeff, 8);
  return copy_result(
    grassmann_pga3_motor_normalize_impl_v1(input), out->coeff, 8);
}

grassmann_status_v1 grassmann_pga3_motor_inverse_v1(
    const grassmann_pga3_motor_v1 *motor,
    grassmann_pga3_motor_v1 *out) {
  if (motor == NULL || out == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  if (!motor_is_valid(
        motor, GRASSMANN_PGA3_MOTOR_VALIDITY_TOLERANCE_V1)) {
    return GRASSMANN_INVALID_MOTOR_V1;
  }
  lean_obj_res input = packed_array(motor->coeff, 8);
  return copy_result(
    grassmann_pga3_motor_inverse_impl_v1(input), out->coeff, 8);
}

grassmann_status_v1 grassmann_pga3_motor_apply_xyz_batch_v1(
    const grassmann_pga3_motor_v1 *motor,
    const double *xyz_in,
    size_t point_count,
    double *xyz_out) {
  if (motor == NULL) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  if (point_count > SIZE_MAX / 3u ||
      point_count > SIZE_MAX / (3u * sizeof(double))) {
    return GRASSMANN_BAD_LENGTH_V1;
  }
  if (point_count != 0 && (xyz_in == NULL || xyz_out == NULL)) {
    return GRASSMANN_NULL_POINTER_V1;
  }
  grassmann_status_v1 status = require_runtime();
  if (status != GRASSMANN_OK_V1) {
    return status;
  }
  if (!motor_is_valid(
        motor, GRASSMANN_PGA3_MOTOR_VALIDITY_TOLERANCE_V1)) {
    return GRASSMANN_INVALID_MOTOR_V1;
  }

  const size_t coordinate_count = point_count * 3u;
  lean_obj_res motor_array = packed_array(motor->coeff, 8);
  lean_obj_res xyz_array = packed_array(xyz_in, coordinate_count);
  return copy_result(
    grassmann_pga3_motor_apply_xyz_batch_impl_v1(motor_array, xyz_array),
    xyz_out,
    coordinate_count);
}
