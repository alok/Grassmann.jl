/*
 * c/cabi_parity_dump.c — Native C ABI parity & benchmark runner for
 * `scripts/bench-cabi-wasm.mjs` (compares exact numeric GA kernels, 69-preset
 * catalog, and structural GSIR v1 frames across Native C ABI, Lean WASM, and
 * pure-Lean `ga-server`).
 */
#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "grassmann/cabi.h"

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec * 1e-6;
}

static uint16_t rd_u16(const uint8_t *p) {
  return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}
static uint32_t rd_u32(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static uint64_t rd_u64(const uint8_t *p) {
  return (uint64_t)rd_u32(p) | ((uint64_t)rd_u32(p + 4) << 32);
}
static float rd_f32(const uint8_t *p) {
  uint32_t u = rd_u32(p);
  float f = 0.0f;
  memcpy(&f, &u, 4);
  return f;
}
static void wr_u16(uint8_t *p, uint16_t v) { p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8); }
static void wr_u32(uint8_t *p, uint32_t v) {
  p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);
  p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
}
static void wr_f32(uint8_t *p, float f) {
  uint32_t u = 0; memcpy(&u, &f, 4); wr_u32(p, u);
}

static void print_f64_arr(const double *a, size_t n) {
  putchar('[');
  for (size_t i = 0; i < n; ++i) {
    if (i) putchar(',');
    printf("%.17g", a[i]);
  }
  putchar(']');
}

static int dispatch_json_grow(
    uint64_t sid, const char *json, uint8_t **buf, uint32_t *cap, uint32_t *got) {
  int32_t rc = grassmann_studio_dispatch_json(sid, json, (uint32_t)strlen(json), *buf, *cap, got);
  if (rc == GSIR_ERR_BUF_SMALL) {
    *cap = *got + 131072u;
    *buf = (uint8_t *)realloc(*buf, *cap);
    rc = grassmann_studio_get_frame(sid, *buf, *cap, got);
  }
  return rc;
}

static int dispatch_bin_grow(
    uint64_t sid, const uint8_t *ev, uint32_t evLen, uint8_t **buf, uint32_t *cap, uint32_t *got) {
  int32_t rc = grassmann_studio_dispatch_bin(sid, ev, evLen, *buf, *cap, got);
  if (rc == GSIR_ERR_BUF_SMALL) {
    *cap = *got + 131072u;
    *buf = (uint8_t *)realloc(*buf, *cap);
    rc = grassmann_studio_get_frame(sid, *buf, *cap, got);
  }
  return rc;
}

static void print_gsir_summary(const char *name, const uint8_t *buf, uint32_t len, int comma) {
  assert(len >= 64 && rd_u32(buf) == 0x52495347u && rd_u16(buf + 4) == 1u);
  uint64_t seq = rd_u64(buf + 8);
  uint32_t secCount = rd_u32(buf + 28);
  uint32_t totalLen = rd_u32(buf + 32);
  uint32_t metaOff = rd_u32(buf + 36);
  uint32_t metaLen = rd_u32(buf + 40);
  assert(totalLen == len);

  uint32_t meshVerts = 0, meshIndices = 0, contourPolys = 0;
  int hasBbox = 0;
  float minX = 1e30f, maxX = -1e30f, minY = 1e30f, maxY = -1e30f, minZ = 1e30f, maxZ = -1e30f;

  printf("%s\"%s\":{\"bytes\":%u,\"seq\":%llu,\"metaLen\":%u,\"sections\":[",
         comma ? "," : "", name, len, (unsigned long long)seq, metaLen);
  for (uint32_t i = 0; i < secCount; ++i) {
    uint32_t off = 64u + i * 16u;
    uint32_t kind = rd_u32(buf + off);
    uint32_t count = rd_u32(buf + off + 4);
    uint32_t bOff = rd_u32(buf + off + 8);
    uint32_t bLen = rd_u32(buf + off + 12);
    printf("%s[%u,%u,%u]", i ? "," : "", kind, count, bLen);
    if (kind == 0x0Bu && count > 0 && bOff + 32 <= len) {
      meshVerts = rd_u32(buf + bOff + 16);
      meshIndices = rd_u32(buf + bOff + 20);
      uint32_t posOff = bOff + 32;
      if (meshVerts > 0 && posOff + meshVerts * 12 <= len) {
        hasBbox = 1;
        for (uint32_t v = 0; v < meshVerts; ++v) {
          float x = rd_f32(buf + posOff + v * 12);
          float y = rd_f32(buf + posOff + v * 12 + 4);
          float z = rd_f32(buf + posOff + v * 12 + 8);
          if (x < minX) minX = x; if (x > maxX) maxX = x;
          if (y < minY) minY = y; if (y > maxY) maxY = y;
          if (z < minZ) minZ = z; if (z > maxZ) maxZ = z;
        }
      }
    } else if (kind == 0x0Fu && bOff + 20 <= len) {
      contourPolys = rd_u32(buf + bOff + 16);
    }
  }
  printf("],\"meshVerts\":%u,\"meshIndices\":%u,\"contourPolys\":%u,\"bbox\":",
         meshVerts, meshIndices, contourPolys);
  if (hasBbox) {
    printf("[%.6g,%.6g,%.6g,%.6g,%.6g,%.6g]", minX, maxX, minY, maxY, minZ, maxZ);
  } else {
    printf("null");
  }
  printf(",\"meta\":");
  if (metaLen > 0) {
    fwrite(buf + metaOff, 1, metaLen, stdout);
  } else {
    printf("null");
  }
  putchar('}');
}

int main(void) {
  assert(grassmann_initialize() == GSIR_OK);

  /* 1. Direct Numeric GA Kernels */
  double staE0[16] = {0}, staE1[16] = {0}, staMul[16] = {0}, staWedge[16] = {0};
  double staBoost[16] = {0}, staBoosted[16] = {0}, staSpWedge[12] = {0};
  staE0[1] = 1.0; staE1[2] = 1.0;
  assert(grassmann_sta_mul(staE0, staE1, staMul) == GSIR_OK);
  assert(grassmann_sta_wedge(staE0, staE1, staWedge) == GSIR_OK);
  assert(grassmann_sta_boost_rotor(0.75, 1.0, 0.0, 0.0, staBoost) == GSIR_OK);
  assert(grassmann_sta_sandwich(staBoost, staE0, staBoosted) == GSIR_OK);
  double staV1[16] = {0}, staV2[16] = {0};
  staV1[2] = 2.0; staV1[4] = -1.0; staV1[8] = 0.5;
  staV2[2] = -0.5; staV2[4] = 1.5; staV2[8] = 3.0;
  assert(grassmann_sta_spatial_wedge(staV1, staV2, staSpWedge) == GSIR_OK);

  double r3Rot[4] = {1.0, 0.0, 0.0, 1.0}, r3Pt[3] = {1.0, 0.5, -2.0}, r3Out[4] = {0};
  assert(grassmann_r3_apply_rational_rotor(r3Rot, r3Pt, r3Out) == GSIR_OK);

  double mR[8] = {0}, mT[8] = {0}, mC[8] = {0}, mMat[16] = {0};
  assert(grassmann_pga3_make_rotor(0.0, 0.0, 1.0, 1.0471975511965976, mR) == GSIR_OK);
  assert(grassmann_pga3_make_translator(1.5, -0.5, 2.25, mT) == GSIR_OK);
  assert(grassmann_pga3_motor_compose(mT, mR, mC) == GSIR_OK);
  assert(grassmann_pga3_motor_to_mat4(mC, mMat) == GSIR_OK);

  double cgaUp[32] = {0}, cgaDown[3] = {0};
  assert(grassmann_cga3_up(1.5, -2.25, 0.75, cgaUp) == GSIR_OK);
  assert(grassmann_cga3_down(cgaUp, cgaDown) == GSIR_OK);

  /* 2. Full 69-Preset Catalog */
  uint32_t catNeed = 0, catGot = 0;
  assert(grassmann_studio_preset_catalog(NULL, 0, &catNeed) == GSIR_ERR_BUF_SMALL);
  char *catBuf = (char *)malloc(catNeed + 1);
  assert(grassmann_studio_preset_catalog(catBuf, catNeed, &catGot) == GSIR_OK);
  catBuf[catGot] = '\0';

  printf("{\"version\":%u,\"kernels\":{\"staMul\":", grassmann_cabi_version());
  print_f64_arr(staMul, 16);
  printf(",\"staBoosted\":"); print_f64_arr(staBoosted, 16);
  printf(",\"staSpWedge\":"); print_f64_arr(staSpWedge, 12);
  printf(",\"r3Rational\":"); print_f64_arr(r3Out, 4);
  printf(",\"pga3Motor\":"); print_f64_arr(mC, 8);
  printf(",\"pga3Mat4\":"); print_f64_arr(mMat, 16);
  printf(",\"cga3Down\":"); print_f64_arr(cgaDown, 3);
  printf("},\"catalog\":%s,\"frames\":{", catBuf);
  free(catBuf);

  /* 3. Canonical GSIR v1 Frame Parity Sequence */
  uint64_t sid = grassmann_studio_create();
  assert(sid > 0);
  uint32_t cap = 524288u, got = 0;
  uint8_t *buf = (uint8_t *)malloc(cap);

  assert(grassmann_studio_get_frame(sid, buf, cap, &got) == GSIR_OK);
  print_gsir_summary("initial_bunny", buf, got, 0);

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"cga3d_opns_cyclide\"}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("cga3d_opns_cyclide", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"pga3d_objects\"}", &buf, &cap, &got) == GSIR_OK);
  uint8_t tick[12] = {0};
  tick[0] = 0x02; wr_u16(tick + 2, 8); wr_f32(tick + 4, 0.016f); wr_f32(tick + 8, 0.5f);
  assert(dispatch_bin_grow(sid, tick, sizeof(tick), &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("objects_hot_tick", buf, got, 1);

  const char *liveScript =
      "{\"op\":\"evalScript\",\"algebra\":\"PGA3\",\"code\":\"@basis PGA3\\nfn mid(a, b) = (a + b) * 0.5\\nlet A = point(-1.0, 0.0, 0.0)\\nlet B = point(1.0, 0.5, 0.0)\\nlet L = A & B\\nlet M = mid(A, B)\\ngraph([0x44aaff, A, B, L, M])\"}";
  assert(dispatch_json_grow(sid, liveScript, &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("livescript_v2", buf, got, 1);

  const char *gyroidMeshJson =
      "{\"op\":\"evalImplicit\",\"expr\":\"cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)\",\"gpuRaymarch\":false,\"gridN\":16}";
  double tGy0 = now_ms();
  assert(dispatch_json_grow(sid, gyroidMeshJson, &buf, &cap, &got) == GSIR_OK);
  double gyroidMs = now_ms() - tGy0;
  print_gsir_summary("implicit_gyroid_mesh", buf, got, 1);

  const char *gyroidGpuJson =
      "{\"op\":\"evalImplicit\",\"expr\":\"cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)\",\"gpuRaymarch\":true}";
  double tGpu0 = now_ms();
  assert(dispatch_json_grow(sid, gyroidGpuJson, &buf, &cap, &got) == GSIR_OK);
  double gpuShaderMs = now_ms() - tGpu0;
  print_gsir_summary("implicit_gyroid_gpu", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"evalParametric\",\"fx\":\"(1.1+0.42*cos(v))*cos(u)\",\"fy\":\"0.42*sin(v)\",\"fz\":\"(1.1+0.42*cos(v))*sin(u)\",\"nu\":32,\"nv\":18}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("parametric_torus", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"wedge_2d\"}", &buf, &cap, &got) == GSIR_OK);
  uint8_t wg[40] = {0};
  wg[0] = 0x06; wr_u16(wg + 2, 36); wr_u32(wg + 4, 2); wr_u32(wg + 8, 3);
  wr_f32(wg + 12, -1.0f); wr_f32(wg + 24, 1.0f); wr_u16(wg + 38, 0);
  assert(dispatch_bin_grow(sid, wg, sizeof(wg), &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("wedge_l1_solved", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"wedgeTutorial\",\"id\":\"T1\"}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("wedge_tutorial_t1", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"wedgeRandom\",\"dim\":3,\"difficulty\":1,\"seed\":42}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("wedge_random_3d", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"calcEval\",\"mode\":\"STA\",\"expr\":\"e1 * e2\"}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("calc_sta", buf, got, 1);

  /* Wave 4B Showcase + @param + 0x0D FLOW_PARTICLES parity */
  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"sta_terrell_penrose\"}", &buf, &cap, &got) == GSIR_OK);
  assert(dispatch_json_grow(sid, "{\"op\":\"setParam\",\"name\":\"beta\",\"value\":0.85}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("terrell_penrose_param", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"sta_maxwell_streamlines\"}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("maxwell_streamlines", buf, got, 1);

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"pga3d_bouncing_cube\"}", &buf, &cap, &got) == GSIR_OK);
  print_gsir_summary("bouncing_cube", buf, got, 1);

  /* 4. Native Microbenchmarks */
  const int N_M = 200000;
  double t0 = now_ms();
  for (int i = 0; i < N_M; ++i) {
    grassmann_pga3_motor_compose(mT, mR, mC);
    mT[0] = mC[0];
  }
  double motorNs = ((now_ms() - t0) * 1e6) / (double)N_M;

  assert(dispatch_json_grow(sid, "{\"op\":\"loadPreset\",\"id\":\"sta_lorentz_boost\"}", &buf, &cap, &got) == GSIR_OK);
  uint8_t drag[20] = {0};
  drag[0] = 0x01; wr_u16(drag + 2, 16); wr_u32(drag + 4, 0);
  const int N_D = 5000;
  t0 = now_ms();
  for (int i = 0; i < N_D; ++i) {
    wr_f32(drag + 8, (float)(i % 100) * 0.01f);
    assert(dispatch_bin_grow(sid, drag, sizeof(drag), &buf, &cap, &got) == GSIR_OK);
  }
  double dragUs = ((now_ms() - t0) * 1e3) / (double)N_D;

  printf("},\"bench\":{\"motorNs\":%.2f,\"dragUs\":%.2f,\"gyroidMs\":%.3f,\"gpuShaderMs\":%.3f}}\n",
         motorNs, dragUs, gyroidMs, gpuShaderMs);

  free(buf);
  grassmann_studio_destroy(sid);
  return 0;
}
