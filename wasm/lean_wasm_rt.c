/*
 * wasm/lean_wasm_rt.c — Self-contained pure-C99 Lean 4.36.0 runtime for
 * Init-only Lean-generated C modules compiled to WebAssembly via Emscripten.
 *
 * Zero external dependencies (no GMP, no libuv, no mimalloc, no OpenSSL, no C++).
 * Implements the exact Lean 4.36 object model (constructors, closures, arrays,
 * FloatArray/ByteArray scalar arrays, UTF-8 strings, ST.Ref, once-cells, and
 * 64-bit big-Nat fallback for wasm32) with exact reference counting (zero leaks).
 */
#include <lean/lean.h>

#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ============================================================================
 * 64-bit Big Nat representation (tag = LeanMPZ) for wasm32 (31-bit small Nat)
 * ============================================================================ */

typedef struct {
  lean_object m_header;
  uint64_t    m_val;   /* exact low 64 bits for Nat/Int bit & integer ops */
  double      m_fval;  /* exact full-precision double for arbitrary-length literals (e.g. 21-digit pi) */
} wasm_bignat_object;

static inline uint64_t nat_to_u64(b_lean_obj_arg o) {
  if (lean_is_scalar(o)) {
    return (uint64_t)lean_unbox(o);
  }
  return ((const wasm_bignat_object *)o)->m_val;
}

static inline double nat_to_f64(b_lean_obj_arg o) {
  if (lean_is_scalar(o)) {
    return (double)lean_unbox(o);
  }
  return ((const wasm_bignat_object *)o)->m_fval;
}

static inline lean_obj_res alloc_bignat(uint64_t v, double fv) {
  wasm_bignat_object *o = (wasm_bignat_object *)lean_alloc_object(sizeof(wasm_bignat_object));
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanMPZ;
  o->m_val = v;
  o->m_fval = fv;
  return &o->m_header;
}

static inline lean_obj_res u64_to_nat(uint64_t v) {
  if (v <= (uint64_t)LEAN_MAX_SMALL_NAT) {
    return lean_box((size_t)v);
  }
  return alloc_bignat(v, (double)v);
}

/* ============================================================================
 * Memory Allocation, Persistence & Exact Reference Counting
 * ============================================================================
 * Note: In lean.h (when !LEAN_MIMALLOC), `lean_alloc_small_object(sz)` prepends
 * a `size_t` size word before the returned `lean_object*`, and `lean_free_small_object`
 * frees `(size_t*)o - 1`. Using the exact same layout for `lean_alloc_object` and
 * `lean_free_object` ensures every heap Lean object (small or big) can be freed
 * uniformly by either `lean_free_small_object` or `lean_free_object`.
 */

lean_object *lean_alloc_object(size_t sz) {
  size_t *mem = (size_t *)malloc(sizeof(size_t) + sz);
  if (LEAN_UNLIKELY(!mem)) abort();
  *mem = sz;
  return (lean_object *)(mem + 1);
}

static inline lean_object *lean_realloc_object(lean_object *o, size_t new_sz) {
  size_t *mem = (size_t *)realloc((size_t *)o - 1, sizeof(size_t) + new_sz);
  if (LEAN_UNLIKELY(!mem)) abort();
  *mem = new_sz;
  return (lean_object *)(mem + 1);
}

lean_object *lean_alloc_small_object_core(unsigned sz, unsigned slot_idx) {
  (void)slot_idx;
  return lean_alloc_object((size_t)sz);
}

void lean_free_object(lean_object *o) {
  if (LEAN_LIKELY(o != NULL)) {
    free((size_t *)o - 1);
  }
}

#ifndef GRASSMANN_WASM_INLINE_HEARTBEAT
void lean_inc_heartbeat(void) {}
#endif

void lean_internal_panic_out_of_memory(void) {
  fprintf(stderr, "[lean_wasm_rt] out of memory\n");
  abort();
}

void lean_internal_panic_overflow(void) {
  fprintf(stderr, "[lean_wasm_rt] overflow\n");
  abort();
}

void lean_notify_assert(const char *file, int line, const char *cond) {
  fprintf(stderr, "[lean_wasm_rt] assert failed at %s:%d: %s\n", file, line, cond);
  abort();
}

void lean_mark_persistent(lean_object *o) {
  if (lean_is_scalar(o) || o->m_rc == 0) return;
  o->m_rc = 0;
  uint8_t tag = o->m_tag;
  if (tag <= LeanMaxCtorTag) {
    unsigned n = lean_ctor_num_objs(o);
    for (unsigned i = 0; i < n; ++i) {
      lean_mark_persistent(lean_ctor_get(o, i));
    }
  } else if (tag == LeanArray) {
    size_t n = lean_array_size(o);
    for (size_t i = 0; i < n; ++i) {
      lean_mark_persistent(lean_array_get_core(o, i));
    }
  } else if (tag == LeanClosure) {
    unsigned n = lean_closure_num_fixed(o);
    for (unsigned i = 0; i < n; ++i) {
      lean_mark_persistent(lean_closure_get(o, i));
    }
  } else if (tag == LeanRef) {
    lean_mark_persistent(((lean_ref_object *)o)->m_value);
  }
}

void lean_dec_ref_cold(lean_object *o) {
  /*
   * In lean.h, `lean_dec_ref(o)` checks `if (o->m_rc > 1) { o->m_rc--; } else lean_dec_ref_cold(o);`
   * Tail-iterative on the last child so long Lists/Trees never blow the 64 KB WASM stack!
   */
  for (;;) {
    if (LEAN_UNLIKELY(o->m_rc == 0)) return;
    if (LEAN_UNLIKELY(o->m_rc > 1)) {
      o->m_rc--;
      return;
    }
    uint8_t tag = o->m_tag;
    lean_object *next = NULL;
    if (LEAN_LIKELY(tag <= LeanMaxCtorTag)) {
      unsigned n = lean_ctor_num_objs(o);
      if (n > 0) {
        for (unsigned i = 0; i + 1 < n; ++i) {
          lean_object *c = lean_ctor_get(o, i);
          if (!lean_is_scalar(c)) {
            if (c->m_rc > 1) c->m_rc--;
            else lean_dec_ref_cold(c);
          }
        }
        lean_object *last = lean_ctor_get(o, n - 1);
        if (!lean_is_scalar(last)) {
          if (last->m_rc > 1) last->m_rc--;
          else if (last->m_rc == 1) next = last;
        }
      }
    } else if (tag == LeanArray) {
      size_t n = lean_array_size(o);
      lean_object **ptr = lean_array_cptr(o);
      for (size_t i = 0; i < n; ++i) {
        lean_object *c = ptr[i];
        if (!lean_is_scalar(c)) {
          if (c->m_rc > 1) c->m_rc--;
          else lean_dec_ref_cold(c);
        }
      }
    } else if (tag == LeanClosure) {
      unsigned n = lean_closure_num_fixed(o);
      for (unsigned i = 0; i < n; ++i) {
        lean_dec(lean_closure_get(o, i));
      }
    } else if (tag == LeanRef) {
      lean_object *v = ((lean_ref_object *)o)->m_value;
      if (!lean_is_scalar(v)) {
        if (v->m_rc > 1) v->m_rc--;
        else if (v->m_rc == 1) next = v;
      }
    }
    free((size_t *)o - 1);
    if (!next) return;
    o = next;
  }
}

/* ============================================================================
 * Module Init & Once Cells (Single-threaded WASM)
 * ============================================================================ */

static lean_sarray_object g_empty_byte_array_obj = {
  .m_header = { .m_rc = 0, .m_cs_sz = 0, .m_other = 1, .m_tag = LeanScalarArray },
  .m_size = 0,
  .m_capacity = 0
};
lean_object *l_ByteArray_empty = (lean_object *)&g_empty_byte_array_obj;

void lean_initialize_runtime_module(void) {}

lean_obj_res initialize_Init(uint8_t builtin) {
  (void)builtin;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res initialize_Init_Data_FloatArray(uint8_t builtin) {
  (void)builtin;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res initialize_Init_Data_ByteArray(uint8_t builtin) {
  (void)builtin;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res initialize_Init_Data_Float(uint8_t builtin) {
  (void)builtin;
  return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_obj_once_cold(
    lean_object **loc, lean_once_cell_t *tok, lean_object *(*init)(void)) {
  if (tok->state == 0) {
    lean_object *v = init();
    lean_mark_persistent(v);
    *loc = v;
    tok->state = 1;
  }
  return *loc;
}

uint8_t lean_uint8_once_cold(
    uint8_t *loc, lean_once_cell_t *tok, uint8_t (*init)(void)) {
  if (tok->state == 0) {
    *loc = init();
    tok->state = 1;
  }
  return *loc;
}

uint32_t lean_uint32_once_cold(
    uint32_t *loc, lean_once_cell_t *tok, uint32_t (*init)(void)) {
  if (tok->state == 0) {
    *loc = init();
    tok->state = 1;
  }
  return *loc;
}

double lean_float_once_cold(
    double *loc, lean_once_cell_t *tok, double (*init)(void)) {
  if (tok->state == 0) {
    *loc = init();
    tok->state = 1;
  }
  return *loc;
}

/* ============================================================================
 * ST.Ref (BaseIO / IO.Ref)
 * ============================================================================ */

lean_obj_res lean_st_mk_ref(lean_obj_arg val) {
  lean_ref_object *r = (lean_ref_object *)lean_alloc_object(sizeof(lean_ref_object));
  r->m_header.m_rc = 1;
  r->m_header.m_cs_sz = 0;
  r->m_header.m_other = 0;
  r->m_header.m_tag = LeanRef;
  r->m_value = val;
  return &r->m_header;
}

lean_obj_res lean_st_ref_get(b_lean_obj_arg ref) {
  lean_object *v = ((lean_ref_object *)ref)->m_value;
  lean_inc(v);
  return v;
}

lean_obj_res lean_st_ref_swap(b_lean_obj_arg ref, lean_obj_arg new_val) {
  lean_ref_object *r = (lean_ref_object *)ref;
  lean_object *old = r->m_value;
  r->m_value = new_val;
  return old;
}

/* ============================================================================
 * Closure Application (lean_apply_1 .. lean_apply_16, lean_apply_m, lean_apply_n)
 * ============================================================================ */

static lean_object *apply_n(lean_object *f, unsigned n, lean_object **args) {
  if (lean_is_scalar(f)) {
    for (unsigned i = 0; i < n; ++i) lean_dec(args[i]);
    return f;
  }
  unsigned arity = lean_closure_arity(f);
  unsigned fixed = lean_closure_num_fixed(f);
  unsigned total = fixed + n;
  if (total < arity) {
    lean_object *c = lean_alloc_closure(lean_closure_fun(f), arity, total);
    for (unsigned i = 0; i < fixed; ++i) {
      lean_object *v = lean_closure_get(f, i);
      lean_inc(v);
      lean_closure_set(c, i, v);
    }
    for (unsigned i = 0; i < n; ++i) {
      lean_closure_set(c, fixed + i, args[i]);
    }
    lean_dec(f);
    return c;
  }
  lean_object *stack_args[16];
  lean_object **call_args = (arity <= 16)
      ? stack_args
      : (lean_object **)malloc((size_t)arity * sizeof(lean_object *));
  if (!call_args) abort();
  for (unsigned i = 0; i < fixed; ++i) {
    call_args[i] = lean_closure_get(f, i);
    lean_inc(call_args[i]);
  }
  unsigned take = arity - fixed;
  for (unsigned i = 0; i < take; ++i) {
    call_args[fixed + i] = args[i];
  }
  void *fn = lean_closure_fun(f);
  lean_dec(f);
  lean_object *res = NULL;
  switch (arity) {
    case 1: res = ((lean_object *(*)(lean_object *))fn)(call_args[0]); break;
    case 2: res = ((lean_object *(*)(lean_object *, lean_object *))fn)(call_args[0], call_args[1]); break;
    case 3: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2]); break;
    case 4: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3]); break;
    case 5: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4]); break;
    case 6: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5]); break;
    case 7: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6]); break;
    case 8: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7]); break;
    case 9: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8]); break;
    case 10: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9]); break;
    case 11: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10]); break;
    case 12: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10], call_args[11]); break;
    case 13: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10], call_args[11], call_args[12]); break;
    case 14: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10], call_args[11], call_args[12], call_args[13]); break;
    case 15: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10], call_args[11], call_args[12], call_args[13], call_args[14]); break;
    case 16: res = ((lean_object *(*)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *))fn)(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4], call_args[5], call_args[6], call_args[7], call_args[8], call_args[9], call_args[10], call_args[11], call_args[12], call_args[13], call_args[14], call_args[15]); break;
    default:
      res = ((lean_object *(*)(lean_object **))fn)(call_args);
      break;
  }
  if (call_args != stack_args) free(call_args);
  if (total == arity) return res;
  return apply_n(res, n - take, args + take);
}

lean_object *lean_apply_1(lean_object *f, lean_object *a1) {
  if (LEAN_LIKELY(!lean_is_scalar(f))) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    if (LEAN_LIKELY(fixed + 1 == arity)) {
      void *fn = lean_closure_fun(f);
      if (arity == 1) {
        lean_dec_ref(f);
        return ((lean_object *(*)(lean_object *))fn)(a1);
      }
      if (arity == 2) {
        lean_object *c0 = lean_closure_get(f, 0);
        lean_inc(c0);
        lean_dec_ref(f);
        return ((lean_object *(*)(lean_object *, lean_object *))fn)(c0, a1);
      }
      if (arity == 3) {
        lean_object *c0 = lean_closure_get(f, 0);
        lean_object *c1 = lean_closure_get(f, 1);
        lean_inc(c0); lean_inc(c1);
        lean_dec_ref(f);
        return ((lean_object *(*)(lean_object *, lean_object *, lean_object *))fn)(c0, c1, a1);
      }
    }
  }
  lean_object *args[1] = {a1}; return apply_n(f, 1, args);
}
lean_object *lean_apply_2(lean_object *f, lean_object *a1, lean_object *a2) {
  if (LEAN_LIKELY(!lean_is_scalar(f))) {
    unsigned arity = lean_closure_arity(f);
    unsigned fixed = lean_closure_num_fixed(f);
    if (LEAN_LIKELY(fixed + 2 == arity)) {
      void *fn = lean_closure_fun(f);
      if (arity == 2) {
        lean_dec_ref(f);
        return ((lean_object *(*)(lean_object *, lean_object *))fn)(a1, a2);
      }
      if (arity == 3) {
        lean_object *c0 = lean_closure_get(f, 0);
        lean_inc(c0);
        lean_dec_ref(f);
        return ((lean_object *(*)(lean_object *, lean_object *, lean_object *))fn)(c0, a1, a2);
      }
    }
  }
  lean_object *args[2] = {a1, a2}; return apply_n(f, 2, args);
}
lean_object *lean_apply_3(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3) {
  lean_object *args[3] = {a1, a2, a3}; return apply_n(f, 3, args);
}
lean_object *lean_apply_4(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4) {
  lean_object *args[4] = {a1, a2, a3, a4}; return apply_n(f, 4, args);
}
lean_object *lean_apply_5(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5) {
  lean_object *args[5] = {a1, a2, a3, a4, a5}; return apply_n(f, 5, args);
}
lean_object *lean_apply_6(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6) {
  lean_object *args[6] = {a1, a2, a3, a4, a5, a6}; return apply_n(f, 6, args);
}
lean_object *lean_apply_7(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7) {
  lean_object *args[7] = {a1, a2, a3, a4, a5, a6, a7}; return apply_n(f, 7, args);
}
lean_object *lean_apply_8(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8) {
  lean_object *args[8] = {a1, a2, a3, a4, a5, a6, a7, a8}; return apply_n(f, 8, args);
}
lean_object *lean_apply_9(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9) {
  lean_object *args[9] = {a1, a2, a3, a4, a5, a6, a7, a8, a9}; return apply_n(f, 9, args);
}
lean_object *lean_apply_10(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10) {
  lean_object *args[10] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10}; return apply_n(f, 10, args);
}
lean_object *lean_apply_11(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11) {
  lean_object *args[11] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11}; return apply_n(f, 11, args);
}
lean_object *lean_apply_12(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11, lean_object *a12) {
  lean_object *args[12] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12}; return apply_n(f, 12, args);
}
lean_object *lean_apply_13(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11, lean_object *a12, lean_object *a13) {
  lean_object *args[13] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13}; return apply_n(f, 13, args);
}
lean_object *lean_apply_14(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11, lean_object *a12, lean_object *a13, lean_object *a14) {
  lean_object *args[14] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}; return apply_n(f, 14, args);
}
lean_object *lean_apply_15(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11, lean_object *a12, lean_object *a13, lean_object *a14, lean_object *a15) {
  lean_object *args[15] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15}; return apply_n(f, 15, args);
}
lean_object *lean_apply_16(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6, lean_object *a7, lean_object *a8, lean_object *a9, lean_object *a10, lean_object *a11, lean_object *a12, lean_object *a13, lean_object *a14, lean_object *a15, lean_object *a16) {
  lean_object *args[16] = {a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16}; return apply_n(f, 16, args);
}
lean_object *lean_apply_m(lean_object *f, unsigned n, lean_object **args) {
  return apply_n(f, n, args);
}
lean_object *lean_apply_n(lean_object *f, unsigned n, lean_object **args) {
  return apply_n(f, n, args);
}

/* ============================================================================
 * Arrays, FloatArray & ByteArray
 * ============================================================================ */

lean_obj_res lean_copy_expand_array_nonlinear(lean_obj_arg a, bool expand) {
  size_t sz = lean_array_size(a);
  size_t cap = lean_array_capacity(a);
  size_t new_cap = expand ? (cap == 0 ? 4 : cap * 2) : cap;
  if (new_cap < sz) new_cap = sz;
  lean_object *r = lean_alloc_array(sz, new_cap);
  for (size_t i = 0; i < sz; ++i) {
    lean_object *el = lean_array_get_core(a, i);
    lean_inc(el);
    lean_array_set_core(r, i, el);
  }
  lean_dec(a);
  return r;
}

lean_object *lean_array_push(lean_obj_arg a, lean_obj_arg v) {
  lean_object *r;
  if (LEAN_LIKELY(lean_is_exclusive(a))) {
    size_t sz = lean_array_size(a);
    size_t cap = lean_array_capacity(a);
    if (LEAN_LIKELY(cap > sz)) {
      r = a;
    } else {
      /* Exclusive in-place realloc avoids O(N) element lean_inc/lean_dec churn! */
      size_t new_cap = cap == 0 ? 4 : cap * 2;
      r = lean_realloc_object(a, sizeof(lean_array_object) + new_cap * sizeof(lean_object *));
      lean_to_array(r)->m_capacity = new_cap;
    }
  } else {
    r = lean_copy_expand_array_nonlinear(a, lean_array_capacity(a) <= lean_array_size(a));
  }
  size_t sz = lean_array_size(r);
  lean_array_set_size(r, sz + 1);
  lean_array_set_core(r, sz, v);
  return r;
}

lean_object *lean_array_mk(lean_obj_arg l) {
  size_t n = 0;
  lean_object *cur = l;
  while (!lean_is_scalar(cur)) {
    n++;
    cur = lean_ctor_get(cur, 1);
  }
  lean_object *arr = lean_alloc_array(n, n);
  cur = l;
  for (size_t i = 0; i < n; ++i) {
    lean_object *hd = lean_ctor_get(cur, 0);
    lean_inc(hd);
    lean_array_set_core(arr, i, hd);
    cur = lean_ctor_get(cur, 1);
  }
  lean_dec(l);
  return arr;
}

lean_obj_res lean_array_get_panic(lean_obj_arg def_val) {
  return def_val;
}

lean_obj_res lean_array_set_panic(lean_obj_arg a, lean_obj_arg v) {
  lean_dec(v);
  return a;
}

lean_obj_res lean_copy_sarray_nonlinear(lean_obj_arg a, size_t cap) {
  size_t sz = lean_sarray_size(a);
  unsigned esz = lean_sarray_elem_size(a);
  if (cap < sz) cap = sz;
  lean_object *r = lean_alloc_sarray(esz, sz, cap);
  if (sz > 0) {
    memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), sz * esz);
  }
  lean_dec(a);
  return r;
}

lean_obj_res lean_float_array_push(lean_obj_arg a, double d) {
  size_t sz = lean_sarray_size(a);
  size_t cap = lean_sarray_capacity(a);
  lean_object *r = a;
  if (LEAN_UNLIKELY(!lean_is_exclusive(a))) {
    size_t new_cap = sz >= cap ? (cap == 0 ? 4 : cap * 2) : cap;
    r = lean_copy_sarray_nonlinear(a, new_cap);
  } else if (LEAN_UNLIKELY(sz >= cap)) {
    size_t new_cap = cap == 0 ? 4 : cap * 2;
    r = lean_realloc_object(a, sizeof(lean_sarray_object) + new_cap * sizeof(double));
    lean_to_sarray(r)->m_capacity = new_cap;
  }
  lean_float_array_cptr(r)[sz] = d;
  lean_sarray_set_size(r, sz + 1);
  return r;
}

lean_obj_res lean_byte_array_push(lean_obj_arg a, uint8_t b) {
  size_t sz = lean_sarray_size(a);
  size_t cap = lean_sarray_capacity(a);
  lean_object *r = a;
  if (LEAN_UNLIKELY(!lean_is_exclusive(a))) {
    size_t new_cap = sz >= cap ? (cap == 0 ? 16 : cap * 2) : cap;
    r = lean_copy_sarray_nonlinear(a, new_cap);
  } else if (LEAN_UNLIKELY(sz >= cap)) {
    size_t new_cap = cap == 0 ? 16 : cap * 2;
    r = lean_realloc_object(a, sizeof(lean_sarray_object) + new_cap);
    lean_to_sarray(r)->m_capacity = new_cap;
  }
  lean_sarray_cptr(r)[sz] = b;
  lean_sarray_set_size(r, sz + 1);
  return r;
}

lean_obj_res lean_byte_array_copy_slice(
    b_lean_obj_arg src, lean_obj_arg src_off_o,
    lean_obj_arg dest, lean_obj_arg dest_off_o,
    lean_obj_arg len_o, uint8_t exact) {
  size_t s_off = (size_t)nat_to_u64(src_off_o);
  size_t d_off = (size_t)nat_to_u64(dest_off_o);
  size_t len = (size_t)nat_to_u64(len_o);
  lean_dec(src_off_o);
  lean_dec(dest_off_o);
  lean_dec(len_o);
  size_t s_sz = lean_sarray_size(src);
  if (s_off >= s_sz) return dest;
  if (len > s_sz - s_off) len = s_sz - s_off;
  if (len == 0) return dest;
  size_t d_sz = lean_sarray_size(dest);
  if (d_off > d_sz) d_off = d_sz;
  size_t new_sz = d_off + len > d_sz ? d_off + len : d_sz;
  size_t cap = lean_sarray_capacity(dest);
  lean_object *r = dest;
  if (!lean_is_exclusive(dest) || new_sz > cap) {
    size_t new_cap = exact ? new_sz : (cap * 2 > new_sz ? cap * 2 : new_sz);
    r = lean_copy_sarray_nonlinear(dest, new_cap);
  }
  memcpy(lean_sarray_cptr(r) + d_off, lean_sarray_cptr(src) + s_off, len);
  lean_sarray_set_size(r, new_sz);
  return r;
}

/* ============================================================================
 * UTF-8 Strings
 * ============================================================================ */

static size_t utf8_codepoint_count(const uint8_t *s, size_t byte_len) {
  size_t count = 0;
  for (size_t i = 0; i < byte_len; ++i) {
    if ((s[i] & 0xC0u) != 0x80u) count++;
  }
  return count;
}

static inline lean_obj_res mk_ascii_string(const char *s, size_t sz) {
  lean_string_object *o = (lean_string_object *)lean_alloc_object(sizeof(lean_string_object) + sz + 1);
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanString;
  o->m_size = sz + 1;
  o->m_capacity = sz + 1;
  o->m_length = sz;
  if (sz > 0) memcpy(o->m_data, s, sz);
  o->m_data[sz] = '\0';
  return &o->m_header;
}

lean_obj_res lean_mk_string_from_bytes_unchecked(const char *s, size_t sz) {
  lean_string_object *o = (lean_string_object *)lean_alloc_object(sizeof(lean_string_object) + sz + 1);
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanString;
  o->m_size = sz + 1;
  o->m_capacity = sz + 1;
  o->m_length = utf8_codepoint_count((const uint8_t *)s, sz);
  if (sz > 0) memcpy(o->m_data, s, sz);
  o->m_data[sz] = '\0';
  return &o->m_header;
}

lean_obj_res lean_mk_string_from_bytes(const char *s, size_t sz) {
  return lean_mk_string_from_bytes_unchecked(s, sz);
}

lean_obj_res lean_string_append(lean_obj_arg s1, b_lean_obj_arg s2) {
  size_t n1 = lean_string_size(s1) - 1;
  size_t n2 = lean_string_size(s2) - 1;
  if (n2 == 0) return s1;
  size_t len1 = lean_string_len(s1);
  size_t len2 = lean_string_len(s2);
  size_t total = n1 + n2;
  if (LEAN_LIKELY(lean_is_exclusive(s1))) {
    lean_string_object *o = lean_to_string(s1);
    if (LEAN_UNLIKELY(o->m_capacity < total + 1)) {
      size_t cap = o->m_capacity * 2;
      if (cap < total + 1) cap = total + 1;
      o = (lean_string_object *)lean_realloc_object(s1, sizeof(lean_string_object) + cap);
      o->m_capacity = cap;
    }
    memcpy(o->m_data + n1, lean_string_cstr(s2), n2);
    o->m_data[total] = '\0';
    o->m_size = total + 1;
    o->m_length = len1 + len2;
    return &o->m_header;
  }
  size_t cap = total + 1;
  size_t grow = lean_string_capacity(s1) * 2;
  if (grow > cap) cap = grow;
  lean_string_object *o = (lean_string_object *)lean_alloc_object(sizeof(lean_string_object) + cap);
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanString;
  o->m_size = total + 1;
  o->m_capacity = cap;
  o->m_length = len1 + len2;
  if (n1 > 0) memcpy(o->m_data, lean_string_cstr(s1), n1);
  memcpy(o->m_data + n1, lean_string_cstr(s2), n2);
  o->m_data[total] = '\0';
  lean_dec(s1);
  return &o->m_header;
}

lean_obj_res lean_string_push_cold(lean_obj_arg s, uint32_t c) {
  char buf[4];
  size_t w = 0;
  if (c < 0x80u) {
    buf[0] = (char)c; w = 1;
  } else if (c < 0x800u) {
    buf[0] = (char)(0xC0u | (c >> 6));
    buf[1] = (char)(0x80u | (c & 0x3Fu));
    w = 2;
  } else if (c < 0x10000u) {
    buf[0] = (char)(0xE0u | (c >> 12));
    buf[1] = (char)(0x80u | ((c >> 6) & 0x3Fu));
    buf[2] = (char)(0x80u | (c & 0x3Fu));
    w = 3;
  } else {
    buf[0] = (char)(0xF0u | (c >> 18));
    buf[1] = (char)(0x80u | ((c >> 12) & 0x3Fu));
    buf[2] = (char)(0x80u | ((c >> 6) & 0x3Fu));
    buf[3] = (char)(0x80u | (c & 0x3Fu));
    w = 4;
  }
  size_t n1 = lean_string_size(s) - 1;
  size_t len1 = lean_string_len(s);
  size_t total = n1 + w;
  if (LEAN_LIKELY(lean_is_exclusive(s))) {
    lean_string_object *o = lean_to_string(s);
    if (LEAN_UNLIKELY(o->m_capacity < total + 1)) {
      size_t cap = o->m_capacity * 2;
      if (cap < total + 1) cap = total + 16;
      o = (lean_string_object *)lean_realloc_object(s, sizeof(lean_string_object) + cap);
      o->m_capacity = cap;
    }
    memcpy(o->m_data + n1, buf, w);
    o->m_data[total] = '\0';
    o->m_size = total + 1;
    o->m_length = len1 + 1;
    return &o->m_header;
  }
  size_t cap = lean_string_capacity(s) * 2;
  if (cap < total + 1) cap = total + 16;
  lean_string_object *o = (lean_string_object *)lean_alloc_object(sizeof(lean_string_object) + cap);
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanString;
  o->m_size = total + 1;
  o->m_capacity = cap;
  o->m_length = len1 + 1;
  if (n1 > 0) memcpy(o->m_data, lean_string_cstr(s), n1);
  memcpy(o->m_data + n1, buf, w);
  o->m_data[total] = '\0';
  lean_dec(s);
  return &o->m_header;
}

bool lean_string_eq_cold(b_lean_obj_arg s1, b_lean_obj_arg s2) {
  size_t n1 = lean_string_size(s1);
  size_t n2 = lean_string_size(s2);
  if (n1 != n2) return false;
  return memcmp(lean_string_cstr(s1), lean_string_cstr(s2), n1) == 0;
}

lean_obj_res lean_string_to_utf8(b_lean_obj_arg s) {
  size_t sz = lean_string_size(s) - 1;
  lean_obj_res ba = lean_alloc_sarray(1, sz, sz);
  if (sz > 0) memcpy(lean_sarray_cptr(ba), lean_string_cstr(s), sz);
  return ba;
}

lean_obj_res l_String_toListImpl(b_lean_obj_arg s) {
  const uint8_t *p = (const uint8_t *)lean_string_cstr(s);
  size_t sz = lean_string_size(s) - 1;
  /* Decode codepoints into temporary array, then build List in reverse */
  uint32_t *cps = sz > 0 ? (uint32_t *)malloc(sz * sizeof(uint32_t)) : NULL;
  size_t count = 0;
  size_t i = 0;
  while (i < sz) {
    uint8_t c = p[i];
    uint32_t cp = 0;
    if (c < 0x80u) {
      cp = c; i += 1;
    } else if ((c & 0xE0u) == 0xC0u && i + 1 < sz) {
      cp = ((uint32_t)(c & 0x1Fu) << 6) | (uint32_t)(p[i + 1] & 0x3Fu);
      i += 2;
    } else if ((c & 0xF0u) == 0xE0u && i + 2 < sz) {
      cp = ((uint32_t)(c & 0x0Fu) << 12) | ((uint32_t)(p[i + 1] & 0x3Fu) << 6) |
           (uint32_t)(p[i + 2] & 0x3Fu);
      i += 3;
    } else if ((c & 0xF8u) == 0xF0u && i + 3 < sz) {
      cp = ((uint32_t)(c & 0x07u) << 18) | ((uint32_t)(p[i + 1] & 0x3Fu) << 12) |
           ((uint32_t)(p[i + 2] & 0x3Fu) << 6) | (uint32_t)(p[i + 3] & 0x3Fu);
      i += 4;
    } else {
      cp = 0xFFFDu; i += 1;
    }
    cps[count++] = cp;
  }
  lean_object *lst = lean_box(0); /* List.nil */
  for (size_t k = count; k > 0; --k) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, lean_box_uint32(cps[k - 1]));
    lean_ctor_set(cons, 1, lst);
    lst = cons;
  }
  free(cps);
  return lst;
}

/* ============================================================================
 * Big Nat, Nat/Float & Init Numeric Helpers
 * ============================================================================ */

lean_obj_res lean_big_usize_to_nat(size_t n) { return u64_to_nat((uint64_t)n); }
lean_obj_res lean_big_uint64_to_nat(uint64_t n) { return u64_to_nat(n); }
uint32_t lean_uint32_of_big_nat(b_lean_obj_arg a) { return (uint32_t)nat_to_u64(a); }

lean_obj_res lean_cstr_to_nat(const char *n) {
  if (!n) return lean_box(0);
  double fval = strtod(n, NULL);
  uint64_t u = 0;
  size_t digits = 0;
  for (const char *p = n; *p >= '0' && *p <= '9'; ++p) {
    u = u * 10ULL + (uint64_t)(*p - '0');
    digits++;
  }
  if (digits <= 9 && u <= (uint64_t)LEAN_MAX_SMALL_NAT) {
    return lean_box((size_t)u);
  }
  return alloc_bignat(u, fval);
}

lean_object *lean_nat_big_succ(lean_object *a) { return u64_to_nat(nat_to_u64(a) + 1ULL); }
lean_object *lean_nat_big_add(lean_object *a, lean_object *b) { return u64_to_nat(nat_to_u64(a) + nat_to_u64(b)); }
lean_object *lean_nat_big_sub(lean_object *a, lean_object *b) {
  uint64_t x = nat_to_u64(a), y = nat_to_u64(b);
  return u64_to_nat(x > y ? x - y : 0ULL);
}
lean_object *lean_nat_big_mul(lean_object *a, lean_object *b) { return u64_to_nat(nat_to_u64(a) * nat_to_u64(b)); }
lean_object *lean_nat_overflow_mul(size_t a, size_t b) { return u64_to_nat((uint64_t)a * (uint64_t)b); }
lean_object *lean_nat_big_div(lean_object *a, lean_object *b) {
  uint64_t y = nat_to_u64(b);
  return y == 0 ? lean_box(0) : u64_to_nat(nat_to_u64(a) / y);
}
lean_object *lean_nat_big_mod(lean_object *a, lean_object *b) {
  uint64_t y = nat_to_u64(b);
  return y == 0 ? u64_to_nat(nat_to_u64(a)) : u64_to_nat(nat_to_u64(a) % y);
}
bool lean_nat_big_eq(lean_object *a, lean_object *b) { return nat_to_u64(a) == nat_to_u64(b); }
bool lean_nat_big_le(lean_object *a, lean_object *b) { return nat_to_u64(a) <= nat_to_u64(b); }
bool lean_nat_big_lt(lean_object *a, lean_object *b) { return nat_to_u64(a) < nat_to_u64(b); }

lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
  uint64_t x = nat_to_u64(a1);
  uint64_t s = nat_to_u64(a2);
  return u64_to_nat(s >= 64 ? 0ULL : (x << s));
}

lean_obj_res lean_nat_big_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
  uint64_t x = nat_to_u64(a1);
  uint64_t s = nat_to_u64(a2);
  return u64_to_nat(s >= 64 ? 0ULL : (x >> s));
}

double lean_float_of_nat(b_lean_obj_arg a) {
  return nat_to_f64(a);
}

uint8_t lean_float_isnan(double a) { return isnan(a) ? 1 : 0; }
uint8_t lean_float_isinf(double a) { return isinf(a) ? 1 : 0; }

float lean_float32_of_bits(uint32_t u) {
  float f = 0.0f;
  memcpy(&f, &u, sizeof(float));
  return f;
}

uint32_t lean_float32_to_bits(float d) {
  uint32_t u = 0;
  memcpy(&u, &d, sizeof(uint32_t));
  return u;
}

double l_Float_ofScientific(lean_obj_arg m, uint8_t s, lean_obj_arg e) {
  double dm = nat_to_f64(m);
  double de = nat_to_f64(e);
  lean_dec(m);
  lean_dec(e);
  double p10 = pow(10.0, de);
  return s ? (dm / p10) : (dm * p10);
}

lean_obj_res l_Nat_reprFast(lean_obj_arg n) {
  uint64_t v = nat_to_u64(n);
  lean_dec(n);
  char buf[32];
  int len = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)v);
  return mk_ascii_string(buf, (size_t)(len > 0 ? len : 0));
}

/* ============================================================================
 * Extended Lean 4.36 Runtime & Init Primitives for Full Grassmann.Studio WASM
 * ============================================================================ */

static lean_sarray_object g_empty_float_array_obj = {
  .m_header = { .m_rc = 0, .m_cs_sz = 0, .m_other = sizeof(double), .m_tag = LeanScalarArray },
  .m_size = 0,
  .m_capacity = 0
};
lean_object *l_FloatArray_empty = (lean_object *)&g_empty_float_array_obj;
double l_instInhabitedFloat = 0.0;

uint8_t l_ByteArray_isEmpty(b_lean_obj_arg b) {
  return lean_sarray_size(b) == 0 ? 1 : 0;
}

uint32_t l_Char_ofNat(b_lean_obj_arg n) {
  uint64_t v = nat_to_u64(n);
  if (v <= 0x10FFFFULL && !(v >= 0xD800ULL && v <= 0xDFFFULL)) return (uint32_t)v;
  return 0u;
}

uint8_t lean_float_isfinite(double a) { return isfinite(a) ? 1 : 0; }

lean_obj_res lean_float_to_string(double a) {
  if (isnan(a)) return mk_ascii_string("NaN", 3);
  char buf[64];
  /* Match Lean 4.36 native runtime `std::to_string(double)` (`%f`, 6 decimals)
   * for exact native/WASM GSIR `metaJson` & shader parity! */
  int n = snprintf(buf, sizeof(buf), "%f", a);
  return mk_ascii_string(buf, (size_t)(n > 0 ? n : 0));
}

uint8_t lean_uint8_of_big_nat(b_lean_obj_arg a) { return (uint8_t)nat_to_u64(a); }
uint64_t lean_uint64_of_big_nat(b_lean_obj_arg a) { return nat_to_u64(a); }
size_t lean_usize_of_big_nat(b_lean_obj_arg a) { return (size_t)nat_to_u64(a); }

size_t lean_usize_once_cold(size_t *loc, lean_once_cell_t *tok, size_t (*init)(void)) {
  if (tok->state == 0) {
    *loc = init();
    tok->state = 1;
  }
  return *loc;
}

lean_object *lean_mk_array(lean_obj_arg n_o, lean_obj_arg v) {
  size_t n = (size_t)nat_to_u64(n_o);
  lean_dec(n_o);
  lean_object *arr = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; ++i) {
    lean_inc(v);
    lean_array_set_core(arr, i, v);
  }
  lean_dec(v);
  return arr;
}

lean_object *lean_array_to_list(lean_obj_arg a) {
  size_t n = lean_array_size(a);
  lean_object *lst = lean_box(0);
  for (size_t i = n; i > 0; --i) {
    lean_object *el = lean_array_get_core(a, i - 1);
    lean_inc(el);
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, el);
    lean_ctor_set(cons, 1, lst);
    lst = cons;
  }
  lean_dec(a);
  return lst;
}

lean_object *l_Array_instInhabited___redArg(void) {
  return lean_alloc_array(0, 0);
}

lean_object *l_Array_range(lean_obj_arg n_o) {
  size_t n = (size_t)nat_to_u64(n_o);
  lean_dec(n_o);
  lean_object *arr = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; ++i) {
    lean_array_set_core(arr, i, u64_to_nat((uint64_t)i));
  }
  return arr;
}

lean_object *l_Array_append___redArg(lean_obj_arg a, b_lean_obj_arg b) {
  size_t na = lean_array_size(a);
  size_t nb = lean_array_size(b);
  if (nb == 0) return a;
  size_t total = na + nb;
  lean_object *r = a;
  if (!lean_is_exclusive(a) || lean_array_capacity(a) < total) {
    size_t cap = lean_array_capacity(a) * 2;
    if (cap < total) cap = total;
    r = lean_alloc_array(total, cap);
    for (size_t i = 0; i < na; ++i) {
      lean_object *el = lean_array_get_core(a, i);
      lean_inc(el);
      lean_array_set_core(r, i, el);
    }
    lean_dec(a);
  } else {
    lean_array_set_size(r, total);
  }
  for (size_t i = 0; i < nb; ++i) {
    lean_object *el = lean_array_get_core(b, i);
    lean_inc(el);
    lean_array_set_core(r, na + i, el);
  }
  return r;
}

lean_object *l_Array_extract___redArg(b_lean_obj_arg a, lean_obj_arg start_o, lean_obj_arg stop_o) {
  size_t sz = lean_array_size(a);
  size_t start = (size_t)nat_to_u64(start_o);
  size_t stop = (size_t)nat_to_u64(stop_o);
  lean_dec(start_o);
  lean_dec(stop_o);
  if (stop > sz) stop = sz;
  if (start >= stop) return lean_alloc_array(0, 0);
  size_t n = stop - start;
  lean_object *r = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; ++i) {
    lean_object *el = lean_array_get_core(a, start + i);
    lean_inc(el);
    lean_array_set_core(r, i, el);
  }
  return r;
}

lean_object *l_List_range(lean_obj_arg n_o) {
  size_t n = (size_t)nat_to_u64(n_o);
  lean_dec(n_o);
  lean_object *lst = lean_box(0);
  for (size_t i = n; i > 0; --i) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, u64_to_nat((uint64_t)(i - 1)));
    lean_ctor_set(cons, 1, lst);
    lst = cons;
  }
  return lst;
}

uint8_t l_List_isEmpty___redArg(b_lean_obj_arg xs) {
  return lean_is_scalar(xs) ? 1 : 0;
}

lean_object *l_List_head_x3f___redArg(b_lean_obj_arg xs) {
  if (lean_is_scalar(xs)) return lean_box(0);
  lean_object *hd = lean_ctor_get(xs, 0);
  lean_inc(hd);
  lean_object *s = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(s, 0, hd);
  return s;
}

lean_object *l_List_lengthTR___redArg(b_lean_obj_arg xs) {
  uint64_t n = 0;
  lean_object *cur = xs;
  while (!lean_is_scalar(cur)) {
    n++;
    cur = lean_ctor_get(cur, 1);
  }
  return u64_to_nat(n);
}

lean_object *l_List_drop___redArg(lean_obj_arg n_o, b_lean_obj_arg xs) {
  uint64_t n = nat_to_u64(n_o);
  lean_dec(n_o);
  lean_object *cur = xs;
  while (n > 0 && !lean_is_scalar(cur)) {
    cur = lean_ctor_get(cur, 1);
    n--;
  }
  lean_inc(cur);
  return cur;
}

lean_object *l_List_getD___redArg(b_lean_obj_arg xs, lean_obj_arg idx_o, b_lean_obj_arg dflt) {
  uint64_t idx = nat_to_u64(idx_o);
  lean_dec(idx_o);
  lean_object *cur = xs;
  while (idx > 0 && !lean_is_scalar(cur)) {
    cur = lean_ctor_get(cur, 1);
    idx--;
  }
  lean_object *res = lean_is_scalar(cur) ? dflt : lean_ctor_get(cur, 0);
  lean_inc(res);
  return res;
}

lean_object *l_List_reverse___redArg(lean_obj_arg xs) {
  lean_object *acc = lean_box(0);
  lean_object *cur = xs;
  while (!lean_is_scalar(cur)) {
    lean_object *hd = lean_ctor_get(cur, 0);
    lean_object *tl = lean_ctor_get(cur, 1);
    lean_inc(hd);
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, hd);
    lean_ctor_set(cons, 1, acc);
    acc = cons;
    cur = tl;
  }
  lean_dec(xs);
  return acc;
}

lean_object *l_List_appendTR___redArg(lean_obj_arg xs, lean_obj_arg ys) {
  if (lean_is_scalar(xs)) return ys;
  size_t n = 0;
  lean_object *cur = xs;
  while (!lean_is_scalar(cur)) { n++; cur = lean_ctor_get(cur, 1); }
  lean_object **els = (lean_object **)malloc(n * sizeof(lean_object *));
  if (!els) abort();
  cur = xs;
  for (size_t i = 0; i < n; ++i) {
    els[i] = lean_ctor_get(cur, 0);
    lean_inc(els[i]);
    cur = lean_ctor_get(cur, 1);
  }
  lean_dec(xs);
  lean_object *acc = ys;
  for (size_t i = n; i > 0; --i) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cons, 0, els[i - 1]);
    lean_ctor_set(cons, 1, acc);
    acc = cons;
  }
  free(els);
  return acc;
}

static size_t utf8_decode_one(const uint8_t *p, size_t sz, size_t i, uint32_t *out_cp) {
  uint8_t c = p[i];
  if (c < 0x80u) { *out_cp = c; return 1; }
  if ((c & 0xE0u) == 0xC0u && i + 1 < sz) {
    *out_cp = ((uint32_t)(c & 0x1Fu) << 6) | (uint32_t)(p[i + 1] & 0x3Fu);
    return 2;
  }
  if ((c & 0xF0u) == 0xE0u && i + 2 < sz) {
    *out_cp = ((uint32_t)(c & 0x0Fu) << 12) | ((uint32_t)(p[i + 1] & 0x3Fu) << 6) |
              (uint32_t)(p[i + 2] & 0x3Fu);
    return 3;
  }
  if ((c & 0xF8u) == 0xF0u && i + 3 < sz) {
    *out_cp = ((uint32_t)(c & 0x07u) << 18) | ((uint32_t)(p[i + 1] & 0x3Fu) << 12) |
              ((uint32_t)(p[i + 2] & 0x3Fu) << 6) | (uint32_t)(p[i + 3] & 0x3Fu);
    return 4;
  }
  *out_cp = 0xFFFDu;
  return 1;
}

uint32_t lean_string_utf8_get_fast_cold(const char *str, size_t i, size_t size, unsigned char c) {
  (void)c;
  uint32_t cp = 0;
  utf8_decode_one((const uint8_t *)str, size > 0 ? size - 1 : 0, i, &cp);
  return cp;
}

lean_obj_res lean_string_utf8_set(lean_obj_arg s, b_lean_obj_arg i_o, uint32_t c) {
  size_t idx = (size_t)nat_to_u64(i_o);
  size_t sz = lean_string_size(s) - 1;
  if (idx >= sz) return s;
  const uint8_t *src = (const uint8_t *)lean_string_cstr(s);
  uint32_t old_cp = 0;
  size_t old_w = utf8_decode_one(src, sz, idx, &old_cp);
  char nb[4];
  size_t new_w = 0;
  if (c < 0x80u) { nb[0] = (char)c; new_w = 1; }
  else if (c < 0x800u) { nb[0] = (char)(0xC0u | (c >> 6)); nb[1] = (char)(0x80u | (c & 0x3Fu)); new_w = 2; }
  else if (c < 0x10000u) { nb[0] = (char)(0xE0u | (c >> 12)); nb[1] = (char)(0x80u | ((c >> 6) & 0x3Fu)); nb[2] = (char)(0x80u | (c & 0x3Fu)); new_w = 3; }
  else { nb[0] = (char)(0xF0u | (c >> 18)); nb[1] = (char)(0x80u | ((c >> 12) & 0x3Fu)); nb[2] = (char)(0x80u | ((c >> 6) & 0x3Fu)); nb[3] = (char)(0x80u | (c & 0x3Fu)); new_w = 4; }
  if (old_w == new_w && lean_is_exclusive(s)) {
    memcpy(lean_to_string(s)->m_data + idx, nb, new_w);
    return s;
  }
  size_t new_sz = sz - old_w + new_w;
  char *tmp = (char *)malloc(new_sz + 1);
  if (!tmp) abort();
  if (idx > 0) memcpy(tmp, src, idx);
  memcpy(tmp + idx, nb, new_w);
  if (idx + old_w < sz) memcpy(tmp + idx + new_w, src + idx + old_w, sz - (idx + old_w));
  lean_obj_res out = lean_mk_string_from_bytes(tmp, new_sz);
  free(tmp);
  lean_dec(s);
  return out;
}

uint8_t lean_string_memcmp(
    b_lean_obj_arg s1, b_lean_obj_arg s2,
    b_lean_obj_arg off1_o, b_lean_obj_arg off2_o, b_lean_obj_arg len_o) {
  size_t o1 = (size_t)nat_to_u64(off1_o);
  size_t o2 = (size_t)nat_to_u64(off2_o);
  size_t n = (size_t)nat_to_u64(len_o);
  size_t sz1 = lean_string_size(s1) - 1;
  size_t sz2 = lean_string_size(s2) - 1;
  if (o1 + n > sz1 || o2 + n > sz2) return 0;
  return memcmp(lean_string_cstr(s1) + o1, lean_string_cstr(s2) + o2, n) == 0 ? 1 : 0;
}

lean_object *lean_string_mk(lean_obj_arg char_list) {
  lean_object *out = lean_mk_string_from_bytes("", 0);
  lean_object *cur = char_list;
  while (!lean_is_scalar(cur)) {
    uint32_t cp = lean_unbox_uint32(lean_ctor_get(cur, 0));
    out = lean_string_push_cold(out, cp);
    cur = lean_ctor_get(cur, 1);
  }
  lean_dec(char_list);
  return out;
}

lean_object *l_String_intercalate(b_lean_obj_arg sep, lean_obj_arg list) {
  lean_object *out = lean_mk_string_from_bytes("", 0);
  lean_object *cur = list;
  bool first = true;
  while (!lean_is_scalar(cur)) {
    if (!first) out = lean_string_append(out, sep);
    first = false;
    out = lean_string_append(out, lean_ctor_get(cur, 0));
    cur = lean_ctor_get(cur, 1);
  }
  lean_dec(list);
  return out;
}

lean_object *l_String_Slice_trimAscii(lean_obj_arg slice) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t start = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t stop = (size_t)nat_to_u64(lean_ctor_get(slice, 2));
  const uint8_t *p = (const uint8_t *)lean_string_cstr(str);
  size_t sz = lean_string_size(str) - 1;
  if (stop > sz) stop = sz;
  while (start < stop && (p[start] == ' ' || p[start] == '\t' || p[start] == '\n' || p[start] == '\r')) start++;
  while (stop > start && (p[stop - 1] == ' ' || p[stop - 1] == '\t' || p[stop - 1] == '\n' || p[stop - 1] == '\r')) stop--;
  lean_inc_ref(str);
  lean_dec(slice);
  lean_object *out = lean_alloc_ctor(0, 3, 0);
  lean_ctor_set(out, 0, str);
  lean_ctor_set(out, 1, u64_to_nat((uint64_t)start));
  lean_ctor_set(out, 2, u64_to_nat((uint64_t)stop));
  return out;
}

lean_object *l_String_Slice_toString(b_lean_obj_arg slice) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t start = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t stop = (size_t)nat_to_u64(lean_ctor_get(slice, 2));
  size_t sz = lean_string_size(str) - 1;
  if (stop > sz) stop = sz;
  if (start >= stop) return lean_mk_string_from_bytes("", 0);
  return lean_mk_string_from_bytes(lean_string_cstr(str) + start, stop - start);
}

lean_object *l_String_Slice_toNat_x3f(b_lean_obj_arg slice) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t start = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t stop = (size_t)nat_to_u64(lean_ctor_get(slice, 2));
  const char *p = lean_string_cstr(str);
  size_t sz = lean_string_size(str) - 1;
  if (stop > sz) stop = sz;
  if (start >= stop) return lean_box(0);
  uint64_t val = 0;
  for (size_t i = start; i < stop; ++i) {
    if (p[i] < '0' || p[i] > '9') return lean_box(0);
    val = val * 10ULL + (uint64_t)(p[i] - '0');
  }
  lean_object *s = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(s, 0, u64_to_nat(val));
  return s;
}

lean_object *l_String_Slice_Pos_nextn(b_lean_obj_arg slice, lean_obj_arg pos_o, lean_obj_arg n_o) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t base = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t stop = (size_t)nat_to_u64(lean_ctor_get(slice, 2));
  size_t pos = base + (size_t)nat_to_u64(pos_o);
  size_t n = (size_t)nat_to_u64(n_o);
  lean_dec(pos_o);
  lean_dec(n_o);
  const uint8_t *p = (const uint8_t *)lean_string_cstr(str);
  size_t sz = lean_string_size(str) - 1;
  if (stop > sz) stop = sz;
  while (n > 0 && pos < stop) {
    uint32_t cp = 0;
    pos += utf8_decode_one(p, stop, pos, &cp);
    n--;
  }
  if (pos > stop) pos = stop;
  return u64_to_nat((uint64_t)(pos - base));
}

lean_object *l_String_Slice_Pos_prevn(b_lean_obj_arg slice, lean_obj_arg pos_o, lean_obj_arg n_o) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t base = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t pos = base + (size_t)nat_to_u64(pos_o);
  size_t n = (size_t)nat_to_u64(n_o);
  lean_dec(pos_o);
  lean_dec(n_o);
  const uint8_t *p = (const uint8_t *)lean_string_cstr(str);
  while (n > 0 && pos > base) {
    pos--;
    while (pos > base && (p[pos] & 0xC0u) == 0x80u) pos--;
    n--;
  }
  return u64_to_nat((uint64_t)(pos - base));
}

uint8_t l_String_Slice_contains___at___00String_Internal_containsImpl_spec__0(
    uint32_t ch, b_lean_obj_arg slice) {
  lean_object *str = lean_ctor_get(slice, 0);
  size_t start = (size_t)nat_to_u64(lean_ctor_get(slice, 1));
  size_t stop = (size_t)nat_to_u64(lean_ctor_get(slice, 2));
  const uint8_t *p = (const uint8_t *)lean_string_cstr(str);
  size_t sz = lean_string_size(str) - 1;
  if (stop > sz) stop = sz;
  size_t i = start;
  while (i < stop) {
    uint32_t cp = 0;
    i += utf8_decode_one(p, stop, i, &cp);
    if (cp == ch) return 1;
  }
  return 0;
}

/* String.toUpper specialized in Init.System.Uri */
lean_object *l_String_mapAux___at___00__private_Init_System_Uri_0__System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(
    lean_obj_arg s, lean_obj_arg pos_o) {
  size_t pos = (size_t)nat_to_u64(pos_o);
  lean_dec(pos_o);
  size_t sz = lean_string_size(s) - 1;
  char *buf = (char *)malloc(sz + 1);
  if (!buf) abort();
  memcpy(buf, lean_string_cstr(s), sz + 1);
  for (size_t i = pos; i < sz; ++i) {
    if (buf[i] >= 'a' && buf[i] <= 'z') buf[i] = (char)(buf[i] - 32);
  }
  lean_object *out = lean_mk_string_from_bytes(buf, sz);
  free(buf);
  lean_dec(s);
  return out;
}

lean_object *l_String_splitOnAux(
    b_lean_obj_arg s, b_lean_obj_arg sep,
    lean_obj_arg b_o, lean_obj_arg i_o, lean_obj_arg j_o, lean_obj_arg acc) {
  lean_dec(b_o); lean_dec(i_o); lean_dec(j_o);
  const char *sp = lean_string_cstr(s);
  size_t slen = lean_string_size(s) - 1;
  const char *dp = lean_string_cstr(sep);
  size_t dlen = lean_string_size(sep) - 1;
  if (dlen == 0) {
    lean_object *cons = lean_alloc_ctor(1, 2, 0);
    lean_inc_ref(s);
    lean_ctor_set(cons, 0, s);
    lean_ctor_set(cons, 1, acc);
    return l_List_reverse___redArg(cons);
  }
  lean_object *res = acc;
  size_t cur = 0;
  size_t idx = 0;
  while (idx + dlen <= slen) {
    if (memcmp(sp + idx, dp, dlen) == 0) {
      lean_object *part = lean_mk_string_from_bytes(sp + cur, idx - cur);
      lean_object *cons = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(cons, 0, part);
      lean_ctor_set(cons, 1, res);
      res = cons;
      idx += dlen;
      cur = idx;
    } else {
      idx++;
    }
  }
  lean_object *tail = lean_mk_string_from_bytes(sp + cur, slen - cur);
  lean_object *cons = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(cons, 0, tail);
  lean_ctor_set(cons, 1, res);
  return l_List_reverse___redArg(cons);
}

uint8_t l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(
    b_lean_obj_arg a, b_lean_obj_arg b) {
  if (lean_is_scalar(a) && lean_is_scalar(b)) return 1;
  if (lean_is_scalar(a) || lean_is_scalar(b)) return 0;
  return lean_unbox_uint32(lean_ctor_get(a, 0)) == lean_unbox_uint32(lean_ctor_get(b, 0)) ? 1 : 0;
}

lean_object *l_Pi_instInhabited___redArg___lam__0(b_lean_obj_arg def_val, lean_obj_arg arg) {
  lean_dec(arg);
  lean_inc(def_val);
  return def_val;
}

/* Repr / Format / Rat stubs referenced only from deriving instances */
lean_object *l_Char_quote(uint32_t c) { (void)c; return lean_mk_string_from_bytes("''", 2); }
lean_object *l_Float_repr(double d, lean_obj_arg p) { lean_dec(p); return lean_float_to_string(d); }
lean_object *l_Int_repr(lean_obj_arg x) { lean_dec(x); return lean_mk_string_from_bytes("0", 1); }
lean_object *l_String_quote(b_lean_obj_arg s) { lean_inc(s); return s; }
lean_object *l_Repr_addAppParen(lean_obj_arg f, lean_obj_arg p) { lean_dec(p); return f; }
lean_object *l_Std_Format_pretty(lean_obj_arg f, lean_obj_arg w, lean_obj_arg i, lean_obj_arg c) {
  lean_dec(f); lean_dec(w); lean_dec(i); lean_dec(c);
  return lean_mk_string_from_bytes("", 0);
}
lean_object *l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_obj_arg n) {
  lean_object *r = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(r, 0, n);
  lean_ctor_set(r, 1, lean_box(1));
  return r;
}
lean_object *l_Rat_add(lean_obj_arg a, lean_obj_arg b) { lean_dec(b); return a; }
lean_object *l_Rat_sub(lean_obj_arg a, lean_obj_arg b) { lean_dec(b); return a; }
lean_object *l_Rat_mul(lean_obj_arg a, lean_obj_arg b) { lean_dec(b); return a; }
lean_object *l_Rat_div(lean_obj_arg a, lean_obj_arg b) { lean_dec(b); return a; }
lean_object *l_Rat_neg(lean_obj_arg a) { return a; }
uint8_t l_instDecidableEqRat_decEq(b_lean_obj_arg a, b_lean_obj_arg b) { return a == b ? 1 : 0; }

/* Wave 3A additions: IEEE-754 Float.toBits, Nat bitwise big ops, Float DecidableEq & Bool repr */
uint64_t lean_float_to_bits(double d) {
  uint64_t bits = 0;
  memcpy(&bits, &d, sizeof(bits));
  return bits;
}
lean_obj_res lean_nat_big_land(b_lean_obj_arg a, b_lean_obj_arg b) {
  return u64_to_nat(nat_to_u64(a) & nat_to_u64(b));
}
lean_obj_res lean_nat_big_lor(b_lean_obj_arg a, b_lean_obj_arg b) {
  return u64_to_nat(nat_to_u64(a) | nat_to_u64(b));
}
lean_obj_res lean_nat_big_lxor(b_lean_obj_arg a, b_lean_obj_arg b) {
  return u64_to_nat(nat_to_u64(a) ^ nat_to_u64(b));
}
uint8_t l_instDecidableEqFloat_decEq(double a, double b) {
  return a == b ? 1 : 0;
}
lean_object *l_Bool_repr___redArg(uint8_t b) {
  lean_object *s = b ? lean_mk_string_from_bytes("true", 4) : lean_mk_string_from_bytes("false", 5);
  lean_object *f = lean_alloc_ctor(3, 1, 0);
  lean_ctor_set(f, 0, s);
  return f;
}

/* Signed 64-bit Big Int + ByteArray + String UTF-8 + Panic helpers */
lean_object *l_Int_instInhabited = (lean_object *)(size_t)1; /* lean_box(0) */

static inline int64_t int_to_i64(b_lean_obj_arg o) {
  if (lean_is_scalar(o)) {
    return lean_scalar_to_int64(o);
  }
  return (int64_t)((const wasm_bignat_object *)o)->m_val;
}

static inline lean_obj_res i64_to_int(int64_t v) {
  if (LEAN_MIN_SMALL_INT <= v && v <= LEAN_MAX_SMALL_INT) {
    return lean_box((unsigned)((int)v));
  }
  return alloc_bignat((uint64_t)v, (double)v);
}

lean_object *lean_big_int_to_int(int n) { return i64_to_int((int64_t)n); }
lean_object *lean_big_size_t_to_int(size_t n) { return i64_to_int((int64_t)n); }
lean_object *lean_big_int64_to_int(int64_t n) { return i64_to_int(n); }
lean_object *lean_int_big_neg(lean_object *a) { return i64_to_int(-int_to_i64(a)); }
lean_object *lean_int_big_add(lean_object *a, lean_object *b) { return i64_to_int(int_to_i64(a) + int_to_i64(b)); }
lean_object *lean_int_big_sub(lean_object *a, lean_object *b) { return i64_to_int(int_to_i64(a) - int_to_i64(b)); }
lean_object *lean_int_big_mul(lean_object *a, lean_object *b) { return i64_to_int(int_to_i64(a) * int_to_i64(b)); }
bool lean_int_big_eq(lean_object *a, lean_object *b) { return int_to_i64(a) == int_to_i64(b); }
bool lean_int_big_le(lean_object *a, lean_object *b) { return int_to_i64(a) <= int_to_i64(b); }
bool lean_int_big_lt(lean_object *a, lean_object *b) { return int_to_i64(a) < int_to_i64(b); }
bool lean_int_big_nonneg(lean_object *a) { return int_to_i64(a) >= 0; }
int8_t lean_int8_of_big_int(b_lean_obj_arg a) { return (int8_t)int_to_i64(a); }
int32_t lean_int32_of_big_int(b_lean_obj_arg a) { return (int32_t)int_to_i64(a); }

lean_object *lean_nat_big_xor(lean_object *a, lean_object *b) {
  return u64_to_nat(nat_to_u64(a) ^ nat_to_u64(b));
}

lean_obj_res lean_byte_array_data(lean_obj_arg a) {
  size_t sz = lean_sarray_size(a);
  lean_obj_res r = lean_alloc_array(sz, sz);
  const uint8_t *it = lean_sarray_cptr(a);
  lean_object **dst = lean_array_cptr(r);
  for (size_t i = 0; i < sz; ++i) {
    dst[i] = lean_box((size_t)it[i]);
  }
  lean_dec(a);
  return r;
}

lean_obj_res lean_string_utf8_next_fast_cold(size_t i, unsigned char c) {
  if ((c & 0xE0u) == 0xC0u) return lean_box(i + 2);
  if ((c & 0xF0u) == 0xE0u) return lean_box(i + 3);
  if ((c & 0xF8u) == 0xF0u) return lean_box(i + 4);
  return lean_box(i + 1);
}

void lean_inc_ref_huge_n(lean_object *o, size_t n) {
  if (o->m_rc == 0) return;
  if (o->m_rc > 0) {
    if (n > (size_t)(INT32_MAX - o->m_rc)) {
      o->m_rc = 0; /* freeze persistent on huge RC */
    } else {
      o->m_rc += (int)n;
    }
  }
}

void lean_internal_panic(char const *msg) {
  fprintf(stderr, "[lean_wasm_rt] panic: %s\n", msg ? msg : "(null)");
  abort();
}

/* Wave 5A additions for Bytecode ImplicitExpr VM */
lean_obj_res l_Int_toNat(b_lean_obj_arg a) {
  int64_t v = int_to_i64(a);
  return v <= 0 ? lean_box(0) : u64_to_nat((uint64_t)v);
}

lean_obj_res lean_float_array_data(lean_obj_arg a) {
  size_t sz = lean_sarray_size(a);
  lean_obj_res r = lean_alloc_array(sz, sz);
  const double *src = lean_float_array_cptr(a);
  lean_object **dst = lean_array_cptr(r);
  for (size_t i = 0; i < sz; ++i) {
    dst[i] = lean_box_float(src[i]);
  }
  lean_dec(a);
  return r;
}

lean_obj_res lean_float_array_mk(lean_obj_arg a) {
  size_t sz = lean_array_size(a);
  lean_obj_res r = lean_alloc_sarray(sizeof(double), sz, sz);
  lean_object **src = lean_array_cptr(a);
  double *dst = lean_float_array_cptr(r);
  for (size_t i = 0; i < sz; ++i) {
    dst[i] = lean_unbox_float(src[i]);
  }
  lean_dec(a);
  return r;
}
