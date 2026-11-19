/*
 * grassmann/cabi.h — Public Init-only C11 / C++17 / Swift ABI for Grassmann.lean
 *
 * Exposes zero `lean_object*` types and pulls zero Lean compiler dependencies.
 * Provides:
 *   1. Canonical `SceneIR` v1 (`GSIR`) stateful Studio session API
 *      (caller-owned output buffers + idempotent `grassmann_studio_get_frame`).
 *   2. Direct packed `double*` numeric GA kernels across STA Cl(3,1) (-+++),
 *      R3 + exact rational rotors, PGA2, PGA3 (motors + batch XYZ), CGA2, CGA3,
 *      and arbitrary Cl(p, q, r) (p+q+r <= 6).
 *
 * PGA3 canonical motor wire order (8 doubles, matching `SCENE_IR_V1.md`):
 *   [0:1, 1:e01, 2:e02, 3:e03, 4:e12, 5:e13, 6:e23, 7:e0123]
 *
 * Credits:
 *   - Michael Reed (chakravala / Grassmann.jl)
 *   - Steven De Keninck (enkimute / ganja.js)
 */
#ifndef GRASSMANN_CABI_H
#define GRASSMANN_CABI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#if defined(_WIN32)
#  ifdef GRASSMANN_CABI_BUILD
#    define GRASSMANN_API __declspec(dllexport)
#  else
#    define GRASSMANN_API __declspec(dllimport)
#  endif
#else
#  define GRASSMANN_API __attribute__((visibility("default")))
#endif

#define GRASSMANN_CABI_VERSION 0x00020000u

/* Canonical GSIR v1 / C ABI status codes (docs/SCENE_IR_V1.md §5). */
#define GSIR_OK             0
#define GSIR_ERR_BAD_HANDLE (-1)
#define GSIR_ERR_BAD_INPUT  (-2)
#define GSIR_ERR_BUF_SMALL  (-3)
#define GSIR_ERR_NOT_INIT   (-4)
#define GSIR_ERR_BAD_RESULT (-5)

/* ============================================================================
 * Runtime Lifecycle
 * ============================================================================ */

GRASSMANN_API uint32_t grassmann_cabi_version(void);
GRASSMANN_API int32_t  grassmann_initialize(void);
GRASSMANN_API int32_t  grassmann_thread_initialize(void);
GRASSMANN_API int32_t  grassmann_thread_finalize(void);

/* ============================================================================
 * Canonical SceneIR v1 (GSIR) Studio Session API
 * ============================================================================
 * Caller allocates one reusable `outBuf` (e.g., 256 KB).
 * If `dispatch_bin` or `dispatch_json` returns `GSIR_ERR_BUF_SMALL`, `*outLen`
 * holds the required byte length and the updated frame is cached in the session;
 * caller grows `outBuf` and calls `grassmann_studio_get_frame` (never re-calling
 * `dispatch_*`, preventing double mutation or lost delta MESH_ASSETS).
 */

GRASSMANN_API uint64_t grassmann_studio_create(void);
GRASSMANN_API void     grassmann_studio_destroy(uint64_t session);

GRASSMANN_API int32_t grassmann_studio_dispatch_bin(
  uint64_t session,
  const uint8_t *eventBuf,
  uint32_t eventLen,
  uint8_t *outBuf,
  uint32_t outCap,
  uint32_t *outLen);

GRASSMANN_API int32_t grassmann_studio_dispatch_json(
  uint64_t session,
  const char *eventJson,
  uint32_t eventLen,
  uint8_t *outBuf,
  uint32_t outCap,
  uint32_t *outLen);

GRASSMANN_API int32_t grassmann_studio_get_frame(
  uint64_t session,
  uint8_t *outBuf,
  uint32_t outCap,
  uint32_t *outLen);

/* ============================================================================
 * Direct Packed Numeric GA Kernels (Caller-Owned Buffers)
 * ============================================================================ */

/* --- Generic Cl(p, q, r), dim = 1 << (p + q + r), p + q + r <= 6 --- */
GRASSMANN_API int32_t grassmann_cl_mul(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, const double *b, double *out);
GRASSMANN_API int32_t grassmann_cl_wedge(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, const double *b, double *out);
GRASSMANN_API int32_t grassmann_cl_join(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, const double *b, double *out);
GRASSMANN_API int32_t grassmann_cl_left_contract(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, const double *b, double *out);
GRASSMANN_API int32_t grassmann_cl_reverse(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, double *out);
GRASSMANN_API int32_t grassmann_cl_dual(
  uint32_t p, uint32_t q, uint32_t r,
  const double *a, double *out);
GRASSMANN_API int32_t grassmann_cl_sandwich(
  uint32_t p, uint32_t q, uint32_t r,
  const double *versor, const double *x, double *out);

/* --- STA Cl(3, 1) (-+++, 16 doubles in bitmask order, ALOK-950 invariants) --- */
GRASSMANN_API int32_t grassmann_sta_mul(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_sta_wedge(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_sta_left_contract(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_sta_reverse(const double a[16], double out[16]);
GRASSMANN_API int32_t grassmann_sta_boost_rotor(double phi, double ux, double uy, double uz, double out[16]);
GRASSMANN_API int32_t grassmann_sta_sandwich(const double r[16], const double x[16], double out[16]);
/* out12: [ax, ay, az, bx, by, bz, nx, ny, nz, area, angleRad, lorentzInner] */
GRASSMANN_API int32_t grassmann_sta_spatial_wedge(const double a[16], const double b[16], double out12[12]);

/* --- R3 Cl(3, 0, 0) (8 doubles) + Exact Rational Rotor (zero sqrt/trig) --- */
GRASSMANN_API int32_t grassmann_r3_mul(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_r3_wedge(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_r3_reverse(const double a[8], double out[8]);
GRASSMANN_API int32_t grassmann_r3_sandwich(const double r[8], const double x[8], double out[8]);
/* rotor4: [s, b12, b13, b23]; xyz: [x, y, z]; out4: [x', y', z', normSq] */
GRASSMANN_API int32_t grassmann_r3_apply_rational_rotor(
  const double rotor4[4], const double xyz[3], double out4[4]);
GRASSMANN_API int32_t grassmann_r3_rational_rotor_cayley(
  double t1, double t2, double t3, double out4[4]);

/* --- PGA2 Cl(2, 0, 1) (8 doubles, e0^2 = 0, e1^2 = e2^2 = +1) --- */
GRASSMANN_API int32_t grassmann_pga2_mul(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_pga2_meet(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_pga2_join(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_pga2_left_contract(const double a[8], const double b[8], double out[8]);
GRASSMANN_API int32_t grassmann_pga2_reverse(const double a[8], double out[8]);
GRASSMANN_API int32_t grassmann_pga2_point(double x, double y, double out[8]);
GRASSMANN_API int32_t grassmann_pga2_line(double a, double b, double c, double out[8]);
GRASSMANN_API int32_t grassmann_pga2_sandwich(const double r[8], const double x[8], double out[8]);

/* --- PGA3 Cl(3, 0, 1) (16-blade full + 8-double canonical motors) --- */
GRASSMANN_API int32_t grassmann_pga3_mul(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_pga3_meet(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_pga3_join(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_pga3_left_contract(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_pga3_reverse(const double a[16], double out[16]);

/* Specialized PGA3 8-double motors: [s, e01, e02, e03, e12, e13, e23, e0123] */
GRASSMANN_API int32_t grassmann_pga3_make_rotor(
  double ax, double ay, double az, double angle, double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_make_translator(
  double tx, double ty, double tz, double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_compose(
  const double a8[8], const double b8[8], double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_reverse(const double m8[8], double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_is_unit(const double m8[8], double tol, int32_t *outIsUnit);
GRASSMANN_API int32_t grassmann_pga3_motor_normalize(const double m8[8], double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_inverse(const double m8[8], double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_exp(const double bivec6[6], double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_log(const double m8[8], double out6[6]);
GRASSMANN_API int32_t grassmann_pga3_motor_slerp(
  const double m0[8], const double m1[8], double t, double out8[8]);
GRASSMANN_API int32_t grassmann_pga3_motor_to_mat4(const double m8[8], double outMat16[16]);
GRASSMANN_API int32_t grassmann_pga3_motor_apply_xyz(
  const double m8[8], const double xyzIn[3], double xyzOut[3]);
GRASSMANN_API int32_t grassmann_pga3_motor_apply_xyz_batch(
  const double m8[8], const double *xyzIn, size_t pointCount, double *xyzOut);

/* --- CGA2 Cl(3, 1) (16 doubles) & CGA3 Cl(4, 1) (32 doubles) --- */
GRASSMANN_API int32_t grassmann_cga2_mul(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_cga2_wedge(const double a[16], const double b[16], double out[16]);
GRASSMANN_API int32_t grassmann_cga2_up(double x, double y, double out[16]);

GRASSMANN_API int32_t grassmann_cga3_mul(const double a[32], const double b[32], double out[32]);
GRASSMANN_API int32_t grassmann_cga3_wedge(const double a[32], const double b[32], double out[32]);
GRASSMANN_API int32_t grassmann_cga3_left_contract(const double a[32], const double b[32], double out[32]);
GRASSMANN_API int32_t grassmann_cga3_reverse(const double a[32], double out[32]);
GRASSMANN_API int32_t grassmann_cga3_sandwich(const double r[32], const double x[32], double out[32]);
GRASSMANN_API int32_t grassmann_cga3_up(double x, double y, double z, double out[32]);
GRASSMANN_API int32_t grassmann_cga3_down(const double p[32], double out3[3]);
GRASSMANN_API int32_t grassmann_cga3_dual_sphere(
  double cx, double cy, double cz, double radius, double out[32]);
GRASSMANN_API int32_t grassmann_cga3_dual_plane(
  double nx, double ny, double nz, double d, double out[32]);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* GRASSMANN_CABI_H */
