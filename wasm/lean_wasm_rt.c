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
  uint64_t    m_val;
} wasm_bignat_object;

static inline uint64_t nat_to_u64(b_lean_obj_arg o) {
  if (lean_is_scalar(o)) {
    return (uint64_t)lean_unbox(o);
  }
  return ((const wasm_bignat_object *)o)->m_val;
}

static inline lean_obj_res u64_to_nat(uint64_t v) {
  if (v <= (uint64_t)LEAN_MAX_SMALL_NAT) {
    return lean_box((size_t)v);
  }
  wasm_bignat_object *o = (wasm_bignat_object *)lean_alloc_object(sizeof(wasm_bignat_object));
  o->m_header.m_rc = 1;
  o->m_header.m_cs_sz = 0;
  o->m_header.m_other = 0;
  o->m_header.m_tag = LeanMPZ;
  o->m_val = v;
  return &o->m_header;
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
  if (!mem) abort();
  *mem = sz;
  return (lean_object *)(mem + 1);
}

lean_object *lean_alloc_small_object_core(unsigned sz, unsigned slot_idx) {
  (void)slot_idx;
  return lean_alloc_object((size_t)sz);
}

void lean_free_object(lean_object *o) {
  if (o != NULL) {
    free((size_t *)o - 1);
  }
}

void lean_inc_heartbeat(void) {}

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
   * Therefore when entering here:
   *   m_rc == 1 => last reference, free recursively!
   *   m_rc == 0 => persistent / static constant, do NOT free!
   */
  if (o->m_rc == 0) return;
  if (o->m_rc > 1) {
    o->m_rc--;
    return;
  }
  uint8_t tag = o->m_tag;
  if (tag <= LeanMaxCtorTag) {
    unsigned n = lean_ctor_num_objs(o);
    for (unsigned i = 0; i < n; ++i) {
      lean_dec(lean_ctor_get(o, i));
    }
  } else if (tag == LeanArray) {
    size_t n = lean_array_size(o);
    for (size_t i = 0; i < n; ++i) {
      lean_dec(lean_array_get_core(o, i));
    }
  } else if (tag == LeanClosure) {
    unsigned n = lean_closure_num_fixed(o);
    for (unsigned i = 0; i < n; ++i) {
      lean_dec(lean_closure_get(o, i));
    }
  } else if (tag == LeanRef) {
    lean_dec(((lean_ref_object *)o)->m_value);
  }
  lean_free_object(o);
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
 * Closure Application (lean_apply_1 .. lean_apply_8)
 * ============================================================================ */

static lean_object *apply_n(lean_object *f, unsigned n, lean_object **args) {
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
  lean_object *call_args[16];
  if (arity > 16) abort();
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
    default: abort();
  }
  if (total == arity) return res;
  return apply_n(res, n - take, args + take);
}

lean_object *lean_apply_1(lean_object *f, lean_object *a1) {
  lean_object *args[1] = {a1}; return apply_n(f, 1, args);
}
lean_object *lean_apply_2(lean_object *f, lean_object *a1, lean_object *a2) {
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
  if (lean_is_exclusive(a)) {
    if (lean_array_capacity(a) > lean_array_size(a)) {
      r = a;
    } else {
      r = lean_copy_expand_array_nonlinear(a, true);
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
  if (!lean_is_exclusive(a) || sz >= cap) {
    size_t new_cap = sz >= cap ? (cap == 0 ? 4 : cap * 2) : cap;
    r = lean_copy_sarray_nonlinear(a, new_cap);
  }
  lean_float_array_cptr(r)[sz] = d;
  lean_sarray_set_size(r, sz + 1);
  return r;
}

lean_obj_res lean_byte_array_push(lean_obj_arg a, uint8_t b) {
  size_t sz = lean_sarray_size(a);
  size_t cap = lean_sarray_capacity(a);
  lean_object *r = a;
  if (!lean_is_exclusive(a) || sz >= cap) {
    size_t new_cap = sz >= cap ? (cap == 0 ? 16 : cap * 2) : cap;
    r = lean_copy_sarray_nonlinear(a, new_cap);
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
  if (lean_is_exclusive(s1) && lean_string_capacity(s1) >= total + 1) {
    lean_string_object *o = lean_to_string(s1);
    memcpy(o->m_data + n1, lean_string_cstr(s2), n2);
    o->m_data[total] = '\0';
    o->m_size = total + 1;
    o->m_length = len1 + len2;
    return s1;
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
  if (lean_is_exclusive(s) && lean_string_capacity(s) >= total + 1) {
    lean_string_object *o = lean_to_string(s);
    memcpy(o->m_data + n1, buf, w);
    o->m_data[total] = '\0';
    o->m_size = total + 1;
    o->m_length = len1 + 1;
    return s;
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
  uint64_t v = strtoull(n, NULL, 10);
  return u64_to_nat(v);
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
  return (double)nat_to_u64(a);
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
  double dm = (double)nat_to_u64(m);
  double de = (double)nat_to_u64(e);
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
  return lean_mk_string_from_bytes(buf, (size_t)(len > 0 ? len : 0));
}
