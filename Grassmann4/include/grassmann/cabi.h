#ifndef GRASSMANN_CABI_H
#define GRASSMANN_CABI_H

#include <stddef.h>
#include <stdint.h>

#if defined(_WIN32)
#  if defined(GRASSMANN_CABI_BUILD)
#    define GRASSMANN_CABI_API __declspec(dllexport)
#  else
#    define GRASSMANN_CABI_API __declspec(dllimport)
#  endif
#elif defined(__GNUC__) || defined(__clang__)
#  define GRASSMANN_CABI_API __attribute__((visibility("default")))
#else
#  define GRASSMANN_CABI_API
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* Encoded as major << 16 | minor. */
#define GRASSMANN_CABI_VERSION_V1 UINT32_C(0x00010001)

typedef int32_t grassmann_status_v1;

#define GRASSMANN_OK_V1              INT32_C(0)
#define GRASSMANN_NULL_POINTER_V1    INT32_C(1)
#define GRASSMANN_NOT_INITIALIZED_V1 INT32_C(2)
#define GRASSMANN_INIT_FAILED_V1     INT32_C(3)
#define GRASSMANN_BAD_RESULT_V1      INT32_C(4)
#define GRASSMANN_BAD_LENGTH_V1      INT32_C(5)
#define GRASSMANN_INVALID_MOTOR_V1   INT32_C(6)

/*
 * Fixed relative Study-condition tolerance used by checked motor operations
 * and batch transforms.
 */
#define GRASSMANN_PGA3_MOTOR_VALIDITY_TOLERANCE_V1 1e-12

/* Native packed order for `MV PGA3 .even`: masks [0,3,5,6,9,10,12,15]. */
typedef struct grassmann_pga3_motor_v1 {
  double coeff[8];
} grassmann_pga3_motor_v1;

/* Native packed order for `MV PGA3 .odd`: masks [1,2,4,7,8,11,13,14]. */
typedef struct grassmann_pga3_point_v1 {
  double coeff[8];
} grassmann_pga3_point_v1;

/*
 * Raw mask identity is the ABI: these names deliberately avoid blade
 * spellings. The packed core uses orientation conventions under which, for
 * example, mask 5 is canonical e13 = -e31, masks 9/10/12 are e10/e20/e30,
 * and mask 13 is e013 = -e031. The semantic channel aliases below describe
 * the tested Euclidean constructor/transform convention without hiding those
 * signs or adding a conversion layer.
 */
enum grassmann_pga3_even_index_v1 {
  GRASSMANN_PGA3_EVEN_MASK_0_V1 = 0,
  GRASSMANN_PGA3_EVEN_MASK_3_V1 = 1,
  GRASSMANN_PGA3_EVEN_MASK_5_V1 = 2,
  GRASSMANN_PGA3_EVEN_MASK_6_V1 = 3,
  GRASSMANN_PGA3_EVEN_MASK_9_V1 = 4,
  GRASSMANN_PGA3_EVEN_MASK_10_V1 = 5,
  GRASSMANN_PGA3_EVEN_MASK_12_V1 = 6,
  GRASSMANN_PGA3_EVEN_MASK_15_V1 = 7
};

enum grassmann_pga3_odd_index_v1 {
  GRASSMANN_PGA3_ODD_MASK_1_V1 = 0,
  GRASSMANN_PGA3_ODD_MASK_2_V1 = 1,
  GRASSMANN_PGA3_ODD_MASK_4_V1 = 2,
  GRASSMANN_PGA3_ODD_MASK_7_V1 = 3,
  GRASSMANN_PGA3_ODD_MASK_8_V1 = 4,
  GRASSMANN_PGA3_ODD_MASK_11_V1 = 5,
  GRASSMANN_PGA3_ODD_MASK_13_V1 = 6,
  GRASSMANN_PGA3_ODD_MASK_14_V1 = 7
};

enum grassmann_pga3_motor_channel_v1 {
  GRASSMANN_PGA3_MOTOR_SCALAR_V1 = GRASSMANN_PGA3_EVEN_MASK_0_V1,
  GRASSMANN_PGA3_MOTOR_ROTATION_Z_V1 = GRASSMANN_PGA3_EVEN_MASK_3_V1,
  GRASSMANN_PGA3_MOTOR_ROTATION_Y_V1 = GRASSMANN_PGA3_EVEN_MASK_5_V1,
  GRASSMANN_PGA3_MOTOR_ROTATION_X_V1 = GRASSMANN_PGA3_EVEN_MASK_6_V1,
  GRASSMANN_PGA3_MOTOR_TRANSLATION_X_V1 = GRASSMANN_PGA3_EVEN_MASK_9_V1,
  GRASSMANN_PGA3_MOTOR_TRANSLATION_Y_V1 = GRASSMANN_PGA3_EVEN_MASK_10_V1,
  GRASSMANN_PGA3_MOTOR_TRANSLATION_Z_V1 = GRASSMANN_PGA3_EVEN_MASK_12_V1,
  GRASSMANN_PGA3_MOTOR_PSEUDOSCALAR_V1 = GRASSMANN_PGA3_EVEN_MASK_15_V1
};

enum grassmann_pga3_point_channel_v1 {
  GRASSMANN_PGA3_POINT_WEIGHT_V1 = GRASSMANN_PGA3_ODD_MASK_7_V1,
  GRASSMANN_PGA3_POINT_Z_V1 = GRASSMANN_PGA3_ODD_MASK_11_V1,
  GRASSMANN_PGA3_POINT_Y_V1 = GRASSMANN_PGA3_ODD_MASK_13_V1,
  GRASSMANN_PGA3_POINT_X_V1 = GRASSMANN_PGA3_ODD_MASK_14_V1
};

GRASSMANN_CABI_API uint32_t grassmann_cabi_version_v1(void);

/*
 * Initialize the process-global Lean runtime and the Grassmann C ABI module.
 * Call this on the main integration thread, before starting worker threads.
 * Calls after the first successful call are harmless. Initialization itself
 * must be externally serialized.
 */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_initialize_v1(void);

/*
 * Attach/detach a foreign worker thread to/from the Lean runtime. These calls
 * are not needed on the thread that called `grassmann_initialize_v1`.
 */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_thread_initialize_v1(void);
GRASSMANN_CABI_API grassmann_status_v1 grassmann_thread_finalize_v1(void);

GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_make_point_v1(
  double x,
  double y,
  double z,
  grassmann_pga3_point_v1 *out);

GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_extract_point_v1(
  const grassmann_pga3_point_v1 *point,
  double out_xyz[3]);

/* The axis is expected to be normalized. The constructor does not normalize it. */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_make_rotor_v1(
  double axis_x,
  double axis_y,
  double axis_z,
  double angle,
  grassmann_pga3_motor_v1 *out);

GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_make_translator_v1(
  double x,
  double y,
  double z,
  grassmann_pga3_motor_v1 *out);

/* `out = after * before`: applying `out` applies `before`, then `after`. */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_compose_v1(
  const grassmann_pga3_motor_v1 *after,
  const grassmann_pga3_motor_v1 *before,
  grassmann_pga3_motor_v1 *out);

/* For a normalized motor, reverse is the multiplicative inverse. */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_reverse_v1(
  const grassmann_pga3_motor_v1 *motor,
  grassmann_pga3_motor_v1 *out);

/*
 * Test both the unit rotor norm and the PGA Study condition. `out_is_unit` is
 * set to either zero or one. A negative or non-finite tolerance reports false.
 */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_is_unit_v1(
  const grassmann_pga3_motor_v1 *motor,
  double tolerance,
  int *out_is_unit);

/*
 * Normalize/invert a finite rigid PGA3 motor. These functions return
 * GRASSMANN_INVALID_MOTOR_V1 when the rotor norm is not finite, invertible,
 * and above the fixed tolerance, or when
 * `abs(2 * study) <= tolerance * rotor_norm_sq` fails using
 * GRASSMANN_PGA3_MOTOR_VALIDITY_TOLERANCE_V1.
 */
GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_normalize_v1(
  const grassmann_pga3_motor_v1 *motor,
  grassmann_pga3_motor_v1 *out);

GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_inverse_v1(
  const grassmann_pga3_motor_v1 *motor,
  grassmann_pga3_motor_v1 *out);

GRASSMANN_CABI_API grassmann_status_v1 grassmann_pga3_motor_apply_point_v1(
  const grassmann_pga3_motor_v1 *motor,
  const grassmann_pga3_point_v1 *point,
  grassmann_pga3_point_v1 *out);

/*
 * Transform `point_count` tightly packed AoS triples
 * `[x0, y0, z0, x1, y1, z1, ...]` in one Lean boundary crossing. Exact
 * in-place operation (`xyz_in == xyz_out`) is supported. The data pointers may
 * be null only when `point_count == 0`; the motor must always be non-null.
 * Counts for which `3 * point_count` would overflow `size_t` return
 * GRASSMANN_BAD_LENGTH_V1. Invalid motors return
 * GRASSMANN_INVALID_MOTOR_V1.
 */
GRASSMANN_CABI_API grassmann_status_v1
grassmann_pga3_motor_apply_xyz_batch_v1(
  const grassmann_pga3_motor_v1 *motor,
  const double *xyz_in,
  size_t point_count,
  double *xyz_out);

#ifdef __cplusplus
} /* extern "C" */

#  if __cplusplus >= 201103L
static_assert(sizeof(grassmann_pga3_motor_v1) == 8 * sizeof(double),
              "unexpected motor ABI padding");
static_assert(sizeof(grassmann_pga3_point_v1) == 8 * sizeof(double),
              "unexpected point ABI padding");
#  endif
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
_Static_assert(sizeof(grassmann_pga3_motor_v1) == 8 * sizeof(double),
               "unexpected motor ABI padding");
_Static_assert(sizeof(grassmann_pga3_point_v1) == 8 * sizeof(double),
               "unexpected point ABI padding");
#endif

#endif /* GRASSMANN_CABI_H */
