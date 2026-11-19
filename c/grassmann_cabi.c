/*
 * c/grassmann_cabi.c — Caller-owned zero-alloc C ABI shim for Grassmann.lean
 *
 * Compiles identically for:
 *   - Native macOS / visionOS / Linux (linked statically with libInit.a + libleanrt.a, ~2.5 MB!)
 *   - Emscripten WebAssembly (linked with wasm/lean_wasm_rt.c, ~100 KB!)
 */
#include <lean/lean.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#ifndef __EMSCRIPTEN__
#include <pthread.h>
#endif

#define GRASSMANN_CABI_BUILD 1
#include "grassmann/cabi.h"

/* Runtime lifecycle hooks exported by libleanrt / wasm runtime */
extern void lean_initialize_runtime_module(void);
#ifndef __EMSCRIPTEN__
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
#endif

/* Generated module initializer for Grassmann/CABI.lean */
extern lean_obj_res initialize_Grassmann_Grassmann_CABI(uint8_t builtin);

/* ============================================================================
 * Private Lean-exported symbols (owned arguments, owned return values)
 * ============================================================================ */

extern lean_obj_res grassmann_lean_cl_mul(uint32_t, uint32_t, uint32_t, lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_wedge(uint32_t, uint32_t, uint32_t, lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_join(uint32_t, uint32_t, uint32_t, lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_left_contract(uint32_t, uint32_t, uint32_t, lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_reverse(uint32_t, uint32_t, uint32_t, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_dual(uint32_t, uint32_t, uint32_t, lean_obj_arg);
extern lean_obj_res grassmann_lean_cl_sandwich(uint32_t, uint32_t, uint32_t, lean_obj_arg, lean_obj_arg);

extern lean_obj_res grassmann_lean_sta_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_sta_wedge(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_sta_left_contract(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_sta_reverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_sta_boost_rotor(double, double, double, double);
extern lean_obj_res grassmann_lean_sta_sandwich(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_sta_spatial_wedge(lean_obj_arg, lean_obj_arg);

extern lean_obj_res grassmann_lean_r3_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_r3_wedge(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_r3_reverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_r3_sandwich(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_r3_apply_rational_rotor(double, double, double, double, double, double, double);
extern lean_obj_res grassmann_lean_r3_rational_rotor_cayley(double, double, double);

extern lean_obj_res grassmann_lean_pga2_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga2_meet(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga2_join(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga2_left_contract(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga2_reverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga2_point(double, double);
extern lean_obj_res grassmann_lean_pga2_line(double, double, double);
extern lean_obj_res grassmann_lean_pga2_sandwich(lean_obj_arg, lean_obj_arg);

extern lean_obj_res grassmann_lean_pga3_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_meet(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_join(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_left_contract(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_reverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_make_rotor(double, double, double, double);
extern lean_obj_res grassmann_lean_pga3_make_translator(double, double, double);
extern lean_obj_res grassmann_lean_pga3_motor_compose(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_reverse(lean_obj_arg);
extern uint8_t      grassmann_lean_pga3_motor_is_unit(lean_obj_arg, double);
extern lean_obj_res grassmann_lean_pga3_motor_normalize(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_inverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_exp(double, double, double, double, double, double);
extern lean_obj_res grassmann_lean_pga3_motor_log(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_slerp(lean_obj_arg, lean_obj_arg, double);
extern lean_obj_res grassmann_lean_pga3_motor_to_mat4(lean_obj_arg);
extern lean_obj_res grassmann_lean_pga3_motor_apply_xyz(lean_obj_arg, double, double, double);
extern lean_obj_res grassmann_lean_pga3_motor_apply_xyz_batch(lean_obj_arg, lean_obj_arg);

extern lean_obj_res grassmann_lean_cga2_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga2_wedge(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga2_up(double, double);

extern lean_obj_res grassmann_lean_cga3_mul(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_wedge(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_left_contract(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_reverse(lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_sandwich(lean_obj_arg, lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_up(double, double, double);
extern lean_obj_res grassmann_lean_cga3_down(lean_obj_arg);
extern lean_obj_res grassmann_lean_cga3_dual_sphere(double, double, double, double);
extern lean_obj_res grassmann_lean_cga3_dual_plane(double, double, double, double);

extern lean_obj_res grassmann_lean_studio_create(void);
extern lean_obj_res grassmann_lean_studio_destroy(uint64_t);
extern lean_obj_res grassmann_lean_studio_dispatch_bin(uint64_t, lean_obj_arg);
extern lean_obj_res grassmann_lean_studio_dispatch_json(uint64_t, lean_obj_arg);
extern lean_obj_res grassmann_lean_studio_get_frame(uint64_t);

/* ============================================================================
 * Internal State & Helpers
 * ============================================================================ */

static int g_runtime_state = 0; /* 0=uninit, 1=ready, -1=failed */

#ifndef __EMSCRIPTEN__
static pthread_mutex_t g_studio_mutex = PTHREAD_MUTEX_INITIALIZER;
#define STUDIO_LOCK()   pthread_mutex_lock(&g_studio_mutex)
#define STUDIO_UNLOCK() pthread_mutex_unlock(&g_studio_mutex)
#else
#define STUDIO_LOCK()   ((void)0)
#define STUDIO_UNLOCK() ((void)0)
#endif

static inline int32_t require_init(void) {
  return g_runtime_state == 1 ? GSIR_OK : GSIR_ERR_NOT_INIT;
}

static inline lean_obj_res make_f64_array(const double *src, size_t count) {
  lean_obj_res out = lean_alloc_sarray(sizeof(double), count, count);
  if (count > 0) {
    memcpy(lean_float_array_cptr(out), src, count * sizeof(double));
  }
  return out;
}

static inline int32_t copy_f64_result(lean_obj_res res, double *dst, size_t expected) {
  if (res == NULL || !lean_is_sarray(res) ||
      lean_sarray_elem_size(res) != sizeof(double) ||
      lean_sarray_size(res) != expected) {
    if (res != NULL) lean_dec(res);
    return GSIR_ERR_BAD_RESULT;
  }
  if (expected > 0) {
    memcpy(dst, lean_float_array_cptr(res), expected * sizeof(double));
  }
  lean_dec(res);
  return GSIR_OK;
}

static inline lean_obj_res make_byte_array(const uint8_t *src, size_t count) {
  lean_obj_res out = lean_alloc_sarray(1, count, count);
  if (count > 0) {
    memcpy(lean_sarray_cptr(out), src, count);
  }
  return out;
}

static int32_t unpack_studio_io_result(
    lean_obj_res io_res,
    uint8_t *outBuf,
    uint32_t outCap,
    uint32_t *outLen) {
  if (io_res == NULL || !lean_io_result_is_ok(io_res)) {
    if (io_res != NULL) lean_dec(io_res);
    return GSIR_ERR_BAD_RESULT;
  }
  lean_object *pair = lean_io_result_get_value(io_res);
  int32_t status = (int32_t)lean_unbox_uint32(lean_ctor_get(pair, 0));
  if (status != GSIR_OK) {
    if (outLen != NULL) *outLen = 0;
    lean_dec_ref(io_res);
    return status;
  }
  lean_object *ba = lean_ctor_get(pair, 1);
  if (!lean_is_sarray(ba) || lean_sarray_elem_size(ba) != 1) {
    lean_dec_ref(io_res);
    return GSIR_ERR_BAD_RESULT;
  }
  size_t sz = lean_sarray_size(ba);
  if (outLen != NULL) *outLen = (uint32_t)sz;
  if (sz > (size_t)outCap || (sz > 0 && outBuf == NULL)) {
    lean_dec_ref(io_res);
    return GSIR_ERR_BUF_SMALL;
  }
  if (sz > 0) {
    memcpy(outBuf, lean_sarray_cptr(ba), sz);
  }
  lean_dec_ref(io_res);
  return GSIR_OK;
}

/* ============================================================================
 * Lifecycle
 * ============================================================================ */

uint32_t grassmann_cabi_version(void) {
  return GRASSMANN_CABI_VERSION;
}

int32_t grassmann_initialize(void) {
  STUDIO_LOCK();
  if (g_runtime_state == 1) {
    STUDIO_UNLOCK();
    return GSIR_OK;
  }
  if (g_runtime_state < 0) {
    STUDIO_UNLOCK();
    return GSIR_ERR_NOT_INIT;
  }
  lean_initialize_runtime_module();
  lean_obj_res res = initialize_Grassmann_Grassmann_CABI(1);
  if (!lean_io_result_is_ok(res)) {
    lean_dec(res);
    g_runtime_state = -1;
    STUDIO_UNLOCK();
    return GSIR_ERR_NOT_INIT;
  }
  lean_dec_ref(res);
#ifndef __EMSCRIPTEN__
  lean_io_mark_end_initialization();
#endif
  g_runtime_state = 1;
  STUDIO_UNLOCK();
  return GSIR_OK;
}

int32_t grassmann_thread_initialize(void) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
#ifndef __EMSCRIPTEN__
  lean_initialize_thread();
#endif
  return GSIR_OK;
}

int32_t grassmann_thread_finalize(void) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
#ifndef __EMSCRIPTEN__
  lean_finalize_thread();
#endif
  return GSIR_OK;
}

/* ============================================================================
 * Canonical SceneIR v1 (GSIR) Studio Session API
 * ============================================================================ */

uint64_t grassmann_studio_create(void) {
  if (g_runtime_state != 1) {
    if (grassmann_initialize() != GSIR_OK) return 0;
  }
  STUDIO_LOCK();
  lean_obj_res res = grassmann_lean_studio_create();
  uint64_t sid = 0;
  if (res != NULL && lean_io_result_is_ok(res)) {
    sid = lean_unbox_uint64(lean_io_result_get_value(res));
  }
  if (res != NULL) lean_dec(res);
  STUDIO_UNLOCK();
  return sid;
}

void grassmann_studio_destroy(uint64_t session) {
  if (g_runtime_state != 1 || session == 0) return;
  STUDIO_LOCK();
  lean_obj_res res = grassmann_lean_studio_destroy(session);
  if (res != NULL) lean_dec(res);
  STUDIO_UNLOCK();
}

int32_t grassmann_studio_dispatch_bin(
    uint64_t session,
    const uint8_t *eventBuf,
    uint32_t eventLen,
    uint8_t *outBuf,
    uint32_t outCap,
    uint32_t *outLen) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (session == 0) return GSIR_ERR_BAD_HANDLE;
  if (eventBuf == NULL || eventLen == 0) return GSIR_ERR_BAD_INPUT;
  STUDIO_LOCK();
  lean_obj_res ev = make_byte_array(eventBuf, (size_t)eventLen);
  lean_obj_res res = grassmann_lean_studio_dispatch_bin(session, ev);
  int32_t rc = unpack_studio_io_result(res, outBuf, outCap, outLen);
  STUDIO_UNLOCK();
  return rc;
}

int32_t grassmann_studio_dispatch_json(
    uint64_t session,
    const char *eventJson,
    uint32_t eventLen,
    uint8_t *outBuf,
    uint32_t outCap,
    uint32_t *outLen) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (session == 0) return GSIR_ERR_BAD_HANDLE;
  if (eventJson == NULL || eventLen == 0) return GSIR_ERR_BAD_INPUT;
  STUDIO_LOCK();
  lean_obj_res jstr = lean_mk_string_from_bytes(eventJson, (size_t)eventLen);
  lean_obj_res res = grassmann_lean_studio_dispatch_json(session, jstr);
  int32_t rc = unpack_studio_io_result(res, outBuf, outCap, outLen);
  STUDIO_UNLOCK();
  return rc;
}

int32_t grassmann_studio_get_frame(
    uint64_t session,
    uint8_t *outBuf,
    uint32_t outCap,
    uint32_t *outLen) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (session == 0) return GSIR_ERR_BAD_HANDLE;
  STUDIO_LOCK();
  lean_obj_res res = grassmann_lean_studio_get_frame(session);
  int32_t rc = unpack_studio_io_result(res, outBuf, outCap, outLen);
  STUDIO_UNLOCK();
  return rc;
}

/* ============================================================================
 * Generic Cl(p, q, r)
 * ============================================================================ */

static inline int32_t cl_dim(uint32_t p, uint32_t q, uint32_t r, size_t *out_dim) {
  uint32_t n = p + q + r;
  if (n > 6u) return GSIR_ERR_BAD_INPUT;
  *out_dim = ((size_t)1u) << n;
  return GSIR_OK;
}

#define DEFINE_CL_BIN(pub_name, lean_name)                                     \
  int32_t pub_name(uint32_t p, uint32_t q, uint32_t r,                         \
                   const double *a, const double *b, double *out) {            \
    int32_t st = require_init();                                               \
    if (st != GSIR_OK) return st;                                              \
    if (!a || !b || !out) return GSIR_ERR_BAD_INPUT;                           \
    size_t dim = 0;                                                            \
    st = cl_dim(p, q, r, &dim);                                                \
    if (st != GSIR_OK) return st;                                              \
    return copy_f64_result(                                                    \
      lean_name(p, q, r, make_f64_array(a, dim), make_f64_array(b, dim)),      \
      out, dim);                                                               \
  }

#define DEFINE_CL_UN(pub_name, lean_name)                                      \
  int32_t pub_name(uint32_t p, uint32_t q, uint32_t r,                         \
                   const double *a, double *out) {                             \
    int32_t st = require_init();                                               \
    if (st != GSIR_OK) return st;                                              \
    if (!a || !out) return GSIR_ERR_BAD_INPUT;                                 \
    size_t dim = 0;                                                            \
    st = cl_dim(p, q, r, &dim);                                                \
    if (st != GSIR_OK) return st;                                              \
    return copy_f64_result(lean_name(p, q, r, make_f64_array(a, dim)), out, dim); \
  }

DEFINE_CL_BIN(grassmann_cl_mul,           grassmann_lean_cl_mul)
DEFINE_CL_BIN(grassmann_cl_wedge,         grassmann_lean_cl_wedge)
DEFINE_CL_BIN(grassmann_cl_join,          grassmann_lean_cl_join)
DEFINE_CL_BIN(grassmann_cl_left_contract, grassmann_lean_cl_left_contract)
DEFINE_CL_UN (grassmann_cl_reverse,       grassmann_lean_cl_reverse)
DEFINE_CL_UN (grassmann_cl_dual,          grassmann_lean_cl_dual)
DEFINE_CL_BIN(grassmann_cl_sandwich,      grassmann_lean_cl_sandwich)

/* ============================================================================
 * Fixed-Dimension Helper Macros
 * ============================================================================ */

#define DEFINE_FIXED_BIN(pub_name, lean_name, N_IN, N_OUT)                     \
  int32_t pub_name(const double a[N_IN], const double b[N_IN], double out[N_OUT]) { \
    int32_t st = require_init();                                               \
    if (st != GSIR_OK) return st;                                              \
    if (!a || !b || !out) return GSIR_ERR_BAD_INPUT;                           \
    return copy_f64_result(                                                    \
      lean_name(make_f64_array(a, N_IN), make_f64_array(b, N_IN)), out, N_OUT);\
  }

#define DEFINE_FIXED_UN(pub_name, lean_name, N_IN, N_OUT)                      \
  int32_t pub_name(const double a[N_IN], double out[N_OUT]) {                  \
    int32_t st = require_init();                                               \
    if (st != GSIR_OK) return st;                                              \
    if (!a || !out) return GSIR_ERR_BAD_INPUT;                                 \
    return copy_f64_result(lean_name(make_f64_array(a, N_IN)), out, N_OUT);    \
  }

/* --- STA Cl(3, 1) --- */
DEFINE_FIXED_BIN(grassmann_sta_mul,           grassmann_lean_sta_mul,           16, 16)
DEFINE_FIXED_BIN(grassmann_sta_wedge,         grassmann_lean_sta_wedge,         16, 16)
DEFINE_FIXED_BIN(grassmann_sta_left_contract, grassmann_lean_sta_left_contract, 16, 16)
DEFINE_FIXED_UN (grassmann_sta_reverse,       grassmann_lean_sta_reverse,       16, 16)
DEFINE_FIXED_BIN(grassmann_sta_sandwich,      grassmann_lean_sta_sandwich,      16, 16)
DEFINE_FIXED_BIN(grassmann_sta_spatial_wedge, grassmann_lean_sta_spatial_wedge, 16, 12)

int32_t grassmann_sta_boost_rotor(double phi, double ux, double uy, double uz, double out[16]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_sta_boost_rotor(phi, ux, uy, uz), out, 16);
}

/* --- R3 Cl(3, 0, 0) + Rational Rotor --- */
DEFINE_FIXED_BIN(grassmann_r3_mul,      grassmann_lean_r3_mul,      8, 8)
DEFINE_FIXED_BIN(grassmann_r3_wedge,    grassmann_lean_r3_wedge,    8, 8)
DEFINE_FIXED_UN (grassmann_r3_reverse,  grassmann_lean_r3_reverse,  8, 8)
DEFINE_FIXED_BIN(grassmann_r3_sandwich, grassmann_lean_r3_sandwich, 8, 8)

int32_t grassmann_r3_apply_rational_rotor(
    const double rotor4[4], const double xyz[3], double out4[4]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!rotor4 || !xyz || !out4) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(
    grassmann_lean_r3_apply_rational_rotor(
      rotor4[0], rotor4[1], rotor4[2], rotor4[3], xyz[0], xyz[1], xyz[2]),
    out4, 4);
}

int32_t grassmann_r3_rational_rotor_cayley(double t1, double t2, double t3, double out4[4]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out4) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_r3_rational_rotor_cayley(t1, t2, t3), out4, 4);
}

/* --- PGA2 Cl(2, 0, 1) --- */
DEFINE_FIXED_BIN(grassmann_pga2_mul,           grassmann_lean_pga2_mul,           8, 8)
DEFINE_FIXED_BIN(grassmann_pga2_meet,          grassmann_lean_pga2_meet,          8, 8)
DEFINE_FIXED_BIN(grassmann_pga2_join,          grassmann_lean_pga2_join,          8, 8)
DEFINE_FIXED_BIN(grassmann_pga2_left_contract, grassmann_lean_pga2_left_contract, 8, 8)
DEFINE_FIXED_UN (grassmann_pga2_reverse,       grassmann_lean_pga2_reverse,       8, 8)
DEFINE_FIXED_BIN(grassmann_pga2_sandwich,      grassmann_lean_pga2_sandwich,      8, 8)

int32_t grassmann_pga2_point(double x, double y, double out[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_pga2_point(x, y), out, 8);
}

int32_t grassmann_pga2_line(double a, double b, double c, double out[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_pga2_line(a, b, c), out, 8);
}

/* --- PGA3 Cl(3, 0, 1) --- */
DEFINE_FIXED_BIN(grassmann_pga3_mul,           grassmann_lean_pga3_mul,           16, 16)
DEFINE_FIXED_BIN(grassmann_pga3_meet,          grassmann_lean_pga3_meet,          16, 16)
DEFINE_FIXED_BIN(grassmann_pga3_join,          grassmann_lean_pga3_join,          16, 16)
DEFINE_FIXED_BIN(grassmann_pga3_left_contract, grassmann_lean_pga3_left_contract, 16, 16)
DEFINE_FIXED_UN (grassmann_pga3_reverse,       grassmann_lean_pga3_reverse,       16, 16)

int32_t grassmann_pga3_make_rotor(double ax, double ay, double az, double angle, double out8[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out8) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_pga3_make_rotor(ax, ay, az, angle), out8, 8);
}

int32_t grassmann_pga3_make_translator(double tx, double ty, double tz, double out8[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out8) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_pga3_make_translator(tx, ty, tz), out8, 8);
}

DEFINE_FIXED_BIN(grassmann_pga3_motor_compose,   grassmann_lean_pga3_motor_compose,   8, 8)
DEFINE_FIXED_UN (grassmann_pga3_motor_reverse,   grassmann_lean_pga3_motor_reverse,   8, 8)
DEFINE_FIXED_UN (grassmann_pga3_motor_normalize, grassmann_lean_pga3_motor_normalize, 8, 8)
DEFINE_FIXED_UN (grassmann_pga3_motor_inverse,   grassmann_lean_pga3_motor_inverse,   8, 8)
DEFINE_FIXED_UN (grassmann_pga3_motor_log,       grassmann_lean_pga3_motor_log,       8, 6)
DEFINE_FIXED_UN (grassmann_pga3_motor_to_mat4,   grassmann_lean_pga3_motor_to_mat4,   8, 16)

int32_t grassmann_pga3_motor_is_unit(const double m8[8], double tol, int32_t *outIsUnit) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!m8 || !outIsUnit || tol < 0.0) return GSIR_ERR_BAD_INPUT;
  *outIsUnit = (int32_t)grassmann_lean_pga3_motor_is_unit(make_f64_array(m8, 8), tol);
  return GSIR_OK;
}

int32_t grassmann_pga3_motor_exp(const double bivec6[6], double out8[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!bivec6 || !out8) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(
    grassmann_lean_pga3_motor_exp(
      bivec6[0], bivec6[1], bivec6[2], bivec6[3], bivec6[4], bivec6[5]),
    out8, 8);
}

int32_t grassmann_pga3_motor_slerp(
    const double m0[8], const double m1[8], double t, double out8[8]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!m0 || !m1 || !out8) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(
    grassmann_lean_pga3_motor_slerp(make_f64_array(m0, 8), make_f64_array(m1, 8), t),
    out8, 8);
}

int32_t grassmann_pga3_motor_apply_xyz(
    const double m8[8], const double xyzIn[3], double xyzOut[3]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!m8 || !xyzIn || !xyzOut) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(
    grassmann_lean_pga3_motor_apply_xyz(
      make_f64_array(m8, 8), xyzIn[0], xyzIn[1], xyzIn[2]),
    xyzOut, 3);
}

int32_t grassmann_pga3_motor_apply_xyz_batch(
    const double m8[8], const double *xyzIn, size_t pointCount, double *xyzOut) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!m8) return GSIR_ERR_BAD_INPUT;
  if (pointCount == 0) return GSIR_OK;
  if (!xyzIn || !xyzOut) return GSIR_ERR_BAD_INPUT;
  size_t n = pointCount * 3;
  return copy_f64_result(
    grassmann_lean_pga3_motor_apply_xyz_batch(make_f64_array(m8, 8), make_f64_array(xyzIn, n)),
    xyzOut, n);
}

/* --- CGA2 & CGA3 --- */
DEFINE_FIXED_BIN(grassmann_cga2_mul,   grassmann_lean_cga2_mul,   16, 16)
DEFINE_FIXED_BIN(grassmann_cga2_wedge, grassmann_lean_cga2_wedge, 16, 16)

int32_t grassmann_cga2_up(double x, double y, double out[16]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_cga2_up(x, y), out, 16);
}

DEFINE_FIXED_BIN(grassmann_cga3_mul,           grassmann_lean_cga3_mul,           32, 32)
DEFINE_FIXED_BIN(grassmann_cga3_wedge,         grassmann_lean_cga3_wedge,         32, 32)
DEFINE_FIXED_BIN(grassmann_cga3_left_contract, grassmann_lean_cga3_left_contract, 32, 32)
DEFINE_FIXED_UN (grassmann_cga3_reverse,       grassmann_lean_cga3_reverse,       32, 32)
DEFINE_FIXED_BIN(grassmann_cga3_sandwich,      grassmann_lean_cga3_sandwich,      32, 32)
DEFINE_FIXED_UN (grassmann_cga3_down,          grassmann_lean_cga3_down,          32, 3)

int32_t grassmann_cga3_up(double x, double y, double z, double out[32]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_cga3_up(x, y, z), out, 32);
}

int32_t grassmann_cga3_dual_sphere(
    double cx, double cy, double cz, double radius, double out[32]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_cga3_dual_sphere(cx, cy, cz, radius), out, 32);
}

int32_t grassmann_cga3_dual_plane(
    double nx, double ny, double nz, double d, double out[32]) {
  int32_t st = require_init();
  if (st != GSIR_OK) return st;
  if (!out) return GSIR_ERR_BAD_INPUT;
  return copy_f64_result(grassmann_lean_cga3_dual_plane(nx, ny, nz, d), out, 32);
}
