/*
 * c/cabi_smoke.c — Comprehensive C11 verification & latency benchmark for
 * Grassmann.lean Init-only C ABI + GSIR v1 Studio Session protocol.
 */
#include "grassmann/cabi.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define CHECK(cond, msg)                                                       \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, (msg));        \
      return 1;                                                                \
    }                                                                          \
  } while (0)

#define CHECK_NEAR(a, b, tol, msg)                                             \
  do {                                                                         \
    double _a = (a), _b = (b);                                                 \
    if (!(fabs(_a - _b) <= (tol))) {                                           \
      fprintf(stderr, "FAIL [%s:%d]: %s (got %.12g, expected %.12g, tol %.2e)\n", \
              __FILE__, __LINE__, (msg), _a, _b, (tol));                       \
      return 1;                                                                \
    }                                                                          \
  } while (0)

static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static uint16_t rd_u16(const uint8_t *p) {
  return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}

static uint32_t rd_u32(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
         ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static uint64_t rd_u64(const uint8_t *p) {
  return (uint64_t)rd_u32(p) | ((uint64_t)rd_u32(p + 4) << 32);
}

static void wr_u16(uint8_t *p, uint16_t v) {
  p[0] = (uint8_t)(v & 0xFF);
  p[1] = (uint8_t)((v >> 8) & 0xFF);
}

static void wr_u32(uint8_t *p, uint32_t v) {
  p[0] = (uint8_t)(v & 0xFF);
  p[1] = (uint8_t)((v >> 8) & 0xFF);
  p[2] = (uint8_t)((v >> 16) & 0xFF);
  p[3] = (uint8_t)((v >> 24) & 0xFF);
}

static void wr_f32(uint8_t *p, float f) {
  uint32_t u = 0;
  memcpy(&u, &f, 4);
  wr_u32(p, u);
}

static int verify_gsir_frame(const uint8_t *buf, uint32_t len, uint64_t *outSeq,
                             uint32_t *outMetaLen, int *outHasMeshAssets) {
  CHECK(len >= 64, "frame < 64B header");
  CHECK(rd_u32(buf + 0) == 0x52495347u, "GSIR magic mismatch");
  CHECK(rd_u16(buf + 4) == 1u, "GSIR version != 1");
  uint64_t seq = rd_u64(buf + 8);
  uint32_t secCount = rd_u32(buf + 28);
  uint32_t totalLen = rd_u32(buf + 32);
  uint32_t metaOff = rd_u32(buf + 36);
  uint32_t metaLen = rd_u32(buf + 40);
  CHECK(totalLen == len, "GSIR totalByteLen != actual len");
  CHECK(64u + secCount * 16u <= len, "GSIR section directory overflows frame");
  if (metaLen > 0) {
    CHECK((metaOff % 8u) == 0u, "metaJsonOffset not 8-byte aligned");
    CHECK(metaOff + metaLen <= len, "metaJson overflows frame");
  }
  int hasAssets = 0;
  for (uint32_t i = 0; i < secCount; ++i) {
    const uint8_t *d = buf + 64u + i * 16u;
    uint32_t kind = rd_u32(d + 0);
    uint32_t count = rd_u32(d + 4);
    uint32_t off = rd_u32(d + 8);
    uint32_t blen = rd_u32(d + 12);
    CHECK((off % 8u) == 0u, "GSIR section byteOffset not 8-byte aligned (#17 fix #1)");
    CHECK(off + blen <= len, "GSIR section overflows frame");
    if (kind == 0x0B && count > 0) {
      hasAssets = 1;
      CHECK((blen % 8u) == 0u, "MESH_ASSETS section length not 8-byte padded");
    }
  }
  if (outSeq) *outSeq = seq;
  if (outMetaLen) *outMetaLen = metaLen;
  if (outHasMeshAssets) *outHasMeshAssets = hasAssets;
  return 0;
}

int main(void) {
  CHECK(grassmann_cabi_version() == GRASSMANN_CABI_VERSION, "version check");
  CHECK(grassmann_initialize() == GSIR_OK, "grassmann_initialize");
  CHECK(grassmann_initialize() == GSIR_OK, "idempotent grassmann_initialize");

  /* 1. STA Cl(3,1) (-+++) invariants */
  {
    double et[16] = {0}, ex[16] = {0}, prod[16] = {0};
    et[1] = 1.0; /* et */
    ex[2] = 1.0; /* ex */
    CHECK(grassmann_sta_mul(et, et, prod) == GSIR_OK, "sta_mul et*et");
    CHECK_NEAR(prod[0], -1.0, 1e-12, "et^2 == -1");
    CHECK(grassmann_sta_mul(ex, ex, prod) == GSIR_OK, "sta_mul ex*ex");
    CHECK_NEAR(prod[0], 1.0, 1e-12, "ex^2 == +1");

    double boost[16] = {0}, boostRev[16] = {0}, id[16] = {0};
    double phi = 0.8;
    CHECK(grassmann_sta_boost_rotor(phi, 1.0, 0.0, 0.0, boost) == GSIR_OK, "sta_boost");
    CHECK(grassmann_sta_reverse(boost, boostRev) == GSIR_OK, "sta_reverse");
    CHECK(grassmann_sta_mul(boost, boostRev, id) == GSIR_OK, "boost * ~boost");
    CHECK_NEAR(id[0], 1.0, 1e-12, "boost * ~boost == 1");

    double v[16] = {0}, vb[16] = {0}, v2[16] = {0};
    v[1] = 2.0; v[2] = 0.5; v[4] = -0.3; v[8] = 0.7;
    double origNorm = -v[1]*v[1] + v[2]*v[2] + v[4]*v[4] + v[8]*v[8];
    CHECK(grassmann_sta_sandwich(boost, v, vb) == GSIR_OK, "sta_sandwich");
    CHECK(grassmann_sta_mul(vb, vb, v2) == GSIR_OK, "boosted v^2");
    CHECK_NEAR(v2[0], origNorm, 1e-11, "Lorentz invariance preserved");

    double a[16] = {0}, b[16] = {0}, sw[12] = {0};
    a[2] = 3.0; /* 3 ex */
    b[4] = 4.0; /* 4 ey */
    CHECK(grassmann_sta_spatial_wedge(a, b, sw) == GSIR_OK, "sta_spatial_wedge");
    CHECK_NEAR(sw[9], 12.0, 1e-12, "STA wedge area == 12");
    CHECK_NEAR(sw[8], 12.0, 1e-12, "STA wedge normal_z == 12");
  }

  /* 2. R3 exact rational rotor (zero-sqrt orthogonality) */
  {
    double rot[4] = {0}, out4[4] = {0};
    CHECK(grassmann_r3_rational_rotor_cayley(0.5, -0.25, 0.75, rot) == GSIR_OK, "cayley");
    double xyz[3] = {1.0, 2.0, -3.0};
    CHECK(grassmann_r3_apply_rational_rotor(rot, xyz, out4) == GSIR_OK, "apply_rational_rotor");
    double lenIn = xyz[0]*xyz[0] + xyz[1]*xyz[1] + xyz[2]*xyz[2];
    double lenOut = out4[0]*out4[0] + out4[1]*out4[1] + out4[2]*out4[2];
    CHECK_NEAR(lenOut, lenIn, 1e-12, "R3 rational rotor preserves Euclidean norm exactly");
  }

  /* 3. PGA2 join & meet incidence */
  {
    double p1[8] = {0}, p2[8] = {0}, line[8] = {0}, inc[8] = {0};
    CHECK(grassmann_pga2_point(1.0, 2.0, p1) == GSIR_OK, "pga2_point p1");
    CHECK(grassmann_pga2_point(4.0, 8.0, p2) == GSIR_OK, "pga2_point p2");
    CHECK(grassmann_pga2_join(p1, p2, line) == GSIR_OK, "pga2_join");
    CHECK(grassmann_pga2_meet(line, p1, inc) == GSIR_OK, "pga2_meet(L, p1)");
    CHECK_NEAR(inc[7], 0.0, 1e-12, "PGA2 incidence L ^ p1 == 0");
    CHECK(grassmann_pga2_meet(line, p2, inc) == GSIR_OK, "pga2_meet(L, p2)");
    CHECK_NEAR(inc[7], 0.0, 1e-12, "PGA2 incidence L ^ p2 == 0");
  }

  /* 4. PGA3 motors: rotor, translator, compose, Study normalize, exp/log, mat4, batch */
  {
    double rot[8], tr[8], mot[8], inv[8], prod[8], mat[16], pOut[3];
    double piHalf = 1.5707963267948966;
    CHECK(grassmann_pga3_make_rotor(0.0, 0.0, 1.0, piHalf, rot) == GSIR_OK, "make_rotor");
    CHECK(grassmann_pga3_make_translator(1.0, 2.0, 3.0, tr) == GSIR_OK, "make_translator");
    CHECK(grassmann_pga3_motor_compose(tr, rot, mot) == GSIR_OK, "motor_compose");
    int32_t isUnit = 0;
    CHECK(grassmann_pga3_motor_is_unit(mot, 1e-9, &isUnit) == GSIR_OK && isUnit == 1, "motor_is_unit");
    CHECK(grassmann_pga3_motor_inverse(mot, inv) == GSIR_OK, "motor_inverse");
    CHECK(grassmann_pga3_motor_compose(mot, inv, prod) == GSIR_OK, "mot * mot^-1");
    CHECK_NEAR(prod[0], 1.0, 1e-12, "mot * mot^-1 scalar == 1");
    for (int i = 1; i < 8; ++i) CHECK_NEAR(prod[i], 0.0, 1e-12, "mot * mot^-1 rest == 0");

    /* Apply T(1,2,3) * Rz(pi/2) to (1, 0, 0) -> Rz gives (0, 1, 0) -> T gives (1, 3, 3) */
    double pIn[3] = {1.0, 0.0, 0.0};
    CHECK(grassmann_pga3_motor_apply_xyz(mot, pIn, pOut) == GSIR_OK, "motor_apply_xyz");
    CHECK_NEAR(pOut[0], 1.0, 1e-12, "T*Rz(1,0,0).x == 1");
    CHECK_NEAR(pOut[1], 3.0, 1e-12, "T*Rz(1,0,0).y == 3");
    CHECK_NEAR(pOut[2], 3.0, 1e-12, "T*Rz(1,0,0).z == 3");

    /* exp(log(mot)) == mot roundtrip */
    double bivec[6], roundtrip[8];
    CHECK(grassmann_pga3_motor_log(mot, bivec) == GSIR_OK, "motor_log");
    CHECK(grassmann_pga3_motor_exp(bivec, roundtrip) == GSIR_OK, "motor_exp");
    for (int i = 0; i < 8; ++i) CHECK_NEAR(roundtrip[i], mot[i], 1e-10, "exp(log(M)) == M");

    /* Study normalization on perturbed motor */
    double dirty[8];
    for (int i = 0; i < 8; ++i) dirty[i] = mot[i] * 2.5;
    dirty[7] += 0.3;
    double normM[8];
    CHECK(grassmann_pga3_motor_normalize(dirty, normM) == GSIR_OK, "motor_normalize");
    CHECK(grassmann_pga3_motor_is_unit(normM, 1e-9, &isUnit) == GSIR_OK && isUnit == 1, "normalized is_unit");
    CHECK(grassmann_pga3_motor_to_mat4(mot, mat) == GSIR_OK, "motor_to_mat4");
    CHECK_NEAR(mat[12], 1.0, 1e-12, "mat4 tx");
    CHECK_NEAR(mat[13], 2.0, 1e-12, "mat4 ty");
    CHECK_NEAR(mat[14], 3.0, 1e-12, "mat4 tz");
  }

  /* 5. CGA3 up/down roundtrip & null property */
  {
    double p[32], p2[32], back[3];
    CHECK(grassmann_cga3_up(1.5, -2.25, 0.75, p) == GSIR_OK, "cga3_up");
    CHECK(grassmann_cga3_mul(p, p, p2) == GSIR_OK, "cga3 p*p");
    CHECK_NEAR(p2[0], 0.0, 1e-12, "CGA3 point is null (p^2 == 0)");
    CHECK(grassmann_cga3_down(p, back) == GSIR_OK, "cga3_down");
    CHECK_NEAR(back[0], 1.5, 1e-12, "cga3_down.x");
    CHECK_NEAR(back[1], -2.25, 1e-12, "cga3_down.y");
    CHECK_NEAR(back[2], 0.75, 1e-12, "cga3_down.z");
  }

  /* 6. Canonical GSIR v1 Studio Session API + all #17 verification invariants */
  {
    /* Verify preset catalog export (19 CoffeeShop presets) */
    uint32_t catNeed = 0;
    CHECK(grassmann_studio_preset_catalog(NULL, 0, &catNeed) == GSIR_ERR_BUF_SMALL,
          "preset_catalog size probe");
    CHECK(catNeed > 1000, "preset catalog non-empty JSON");
    char *catBuf = (char *)malloc(catNeed + 1);
    CHECK(catBuf != NULL, "malloc catBuf");
    uint32_t catGot = 0;
    CHECK(grassmann_studio_preset_catalog(catBuf, catNeed, &catGot) == GSIR_OK, "preset_catalog ok");
    catBuf[catGot] = '\0';
    CHECK(strstr(catBuf, "pga3d_slicing") != NULL &&
          strstr(catBuf, "cga3d_opns_cyclide") != NULL &&
          strstr(catBuf, "sta_lorentz_boost") != NULL,
          "preset catalog lists flagship presets");
    free(catBuf);

    uint64_t sid = grassmann_studio_create();
    CHECK(sid != 0, "studio_create");

    /* Small buffer probe -> GSIR_ERR_BUF_SMALL, then idempotent get_frame! */
    uint8_t tiny[32];
    uint32_t need = 0;
    CHECK(grassmann_studio_get_frame(sid, tiny, sizeof(tiny), &need) == GSIR_ERR_BUF_SMALL,
          "small buf returns GSIR_ERR_BUF_SMALL");
    CHECK(need > 64, "need > 64");

    uint32_t cap = need + 131072u;
    uint8_t *buf = (uint8_t *)malloc(cap);
    CHECK(buf != NULL, "malloc frame buf");

    uint32_t got = 0;
    CHECK(grassmann_studio_get_frame(sid, buf, cap, &got) == GSIR_OK, "get_frame ok");
    uint64_t seq0 = 0;
    uint32_t meta0 = 0;
    int hasAssets0 = 0;
    CHECK(verify_gsir_frame(buf, got, &seq0, &meta0, &hasAssets0) == 0, "verify initial sculpted bunny frame");
    CHECK(seq0 == 1, "initial frameSeq == 1");
    CHECK(meta0 > 0, "initial frame carries metaJson");
    CHECK(hasAssets0 == 1, "initial pga3d_slicing frame carries MESH_ASSETS");

    /* Load static-mesh/static-meta pga3d_objects to verify hot Tick omits BOTH MESH_ASSETS & metaJson! */
    const char *loadObj = "{\"op\":\"loadPreset\",\"id\":\"pga3d_objects\"}";
    CHECK(grassmann_studio_dispatch_json(sid, loadObj, (uint32_t)strlen(loadObj), buf, cap, &got) == GSIR_OK,
          "load pga3d_objects");
    uint64_t seqObj = 0; uint32_t metaObj = 0; int assetsObj = 0;
    CHECK(verify_gsir_frame(buf, got, &seqObj, &metaObj, &assetsObj) == 0, "verify objects frame");
    CHECK(assetsObj == 1 && metaObj > 0, "objects full load has assets & meta");

    /* Hot binary Tick -> GSIR_ERR_BUF_SMALL on tiny buf, then idempotent get_frame! */
    uint8_t tickEv[12] = {0};
    tickEv[0] = 0x02; /* Tick */
    tickEv[1] = 0x00; /* no forceFull */
    wr_u16(tickEv + 2, 8);
    wr_f32(tickEv + 4, 0.016f);
    wr_f32(tickEv + 8, 0.5f);
    CHECK(grassmann_studio_dispatch_bin(sid, tickEv, sizeof(tickEv), tiny, sizeof(tiny), &need) == GSIR_ERR_BUF_SMALL,
          "dispatch_bin small buf");
    /* Retry via get_frame MUST NOT double-increment seq! */
    CHECK(grassmann_studio_get_frame(sid, buf, cap, &got) == GSIR_OK, "get_frame after small buf");
    uint64_t seq1 = 0;
    uint32_t meta1 = 0;
    int hasAssets1 = 0;
    CHECK(verify_gsir_frame(buf, got, &seq1, &meta1, &hasAssets1) == 0, "verify tick frame");
    CHECK(seq1 == seqObj + 1, "idempotent get_frame did not double-mutate");
    CHECK(meta1 == 0, "hot tick frame omits unchanged metaJson (metaLen == 0)");
    CHECK(hasAssets1 == 0, "hot tick frame omits cached MESH_ASSETS");

    /* forceFullSnapshot (flags bit 0) restores MESH_ASSETS + metaJson! */
    tickEv[1] = 0x01;
    CHECK(grassmann_studio_dispatch_bin(sid, tickEv, sizeof(tickEv), buf, cap, &got) == GSIR_OK,
          "dispatch_bin forceFullSnapshot");
    uint64_t seq2 = 0;
    uint32_t meta2 = 0;
    int hasAssets2 = 0;
    CHECK(verify_gsir_frame(buf, got, &seq2, &meta2, &hasAssets2) == 0, "verify full snapshot");
    CHECK(seq2 == seq1 + 1 && meta2 > 0 && hasAssets2 == 1, "forceFullSnapshot restored assets & meta");

    /* Test flagship CoffeeShop presets, Wedge 2D/3D, evalScript, evalSurface, evalEquations, calcEval */
    const char *events[] = {
      "{\"op\":\"loadPreset\",\"id\":\"pga3d_slicing\"}",
      "{\"op\":\"loadPreset\",\"id\":\"pga3d_slicing_hq\"}",
      "{\"op\":\"loadPreset\",\"id\":\"pga3d_physics_free_top\"}",
      "{\"op\":\"loadPreset\",\"id\":\"pga3d_origami\"}",
      "{\"op\":\"loadPreset\",\"id\":\"pga3d_motor_orbits\"}",
      "{\"op\":\"loadPreset\",\"id\":\"cga3d_intersections\"}",
      "{\"op\":\"loadPreset\",\"id\":\"cga3d_spheres_apollonius\"}",
      "{\"op\":\"loadPreset\",\"id\":\"cga3d_opns_cyclide\"}",
      "{\"op\":\"loadPreset\",\"id\":\"implicit_gyroid\"}",
      "{\"op\":\"loadPreset\",\"id\":\"param_klein_bottle\"}",
      "{\"op\":\"loadPreset\",\"id\":\"qcga3d_quadrics\"}",
      "{\"op\":\"loadPreset\",\"id\":\"sta_lorentz_boost\"}",
      "{\"op\":\"loadPreset\",\"id\":\"sta_maxwell_em\"}",
      "{\"op\":\"loadPreset\",\"id\":\"r3_rational_rotor\"}",
      "{\"op\":\"loadPreset\",\"id\":\"wedge_2d\"}",
      "{\"op\":\"loadPreset\",\"id\":\"wedge_3d\"}",
      "{\"op\":\"wedgeTutorial\",\"id\":\"T1\"}",
      "{\"op\":\"wedgeTutorial\",\"id\":\"T6\"}",
      "{\"op\":\"wedgeRandom\",\"dim\":2,\"difficulty\":1,\"seed\":42}",
      "{\"op\":\"wedgeRandom\",\"dim\":3,\"difficulty\":2,\"seed\":99}",
      "{\"op\":\"evalScript\",\"algebra\":\"PGA3\",\"code\":\"let P = point(1,2,3); P\"}",
      "{\"op\":\"evalSurface\",\"expr\":\"cos(x)*sin(y)\",\"bounds\":[-2,2,-2,2],\"gridN\":24}",
      "{\"op\":\"evalEquations\",\"equations\":[\"x^2+y^2-1\",\"y-x\"],\"bounds\":[-2,2,-2,2],\"gridN\":32}",
      "{\"op\":\"evalImplicit\",\"expr\":\"cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)\",\"gpuRaymarch\":false}",
      "{\"op\":\"evalImplicit\",\"expr\":\"cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)\",\"gpuRaymarch\":true}",
      "{\"op\":\"evalParametric\",\"fx\":\"(1.1+0.4*cos(v))*cos(u)\",\"fy\":\"0.4*sin(v)\",\"fz\":\"(1.1+0.4*cos(v))*sin(u)\"}",
      "{\"op\":\"calcEval\",\"mode\":\"STA\",\"expr\":\"e1 * e2\"}"
    };
    for (size_t i = 0; i < sizeof(events) / sizeof(events[0]); ++i) {
      int32_t rc = grassmann_studio_dispatch_json(
          sid, events[i], (uint32_t)strlen(events[i]), buf, cap, &got);
      if (rc == GSIR_ERR_BUF_SMALL) {
        cap = got + 131072u;
        buf = (uint8_t *)realloc(buf, cap);
        rc = grassmann_studio_get_frame(sid, buf, cap, &got);
      }
      CHECK(rc == GSIR_OK, "dispatch_json studio event");
      CHECK(verify_gsir_frame(buf, got, NULL, NULL, NULL) == 0, "verify studio frame");
    }

    free(buf);
    grassmann_studio_destroy(sid);
  }

  /* 7. Crossing & Throughput Benchmarks */
  {
    double m0[8], m1[8], out[8];
    grassmann_pga3_make_rotor(0.0, 1.0, 0.0, 0.5, m0);
    grassmann_pga3_make_translator(1.0, 2.0, 3.0, m1);
    const int N = 200000;
    double t0 = now_ns();
    for (int i = 0; i < N; ++i) {
      grassmann_pga3_motor_compose(m0, m1, out);
      m0[0] = out[0];
    }
    double dt = now_ns() - t0;
    printf("[bench] pga3_motor_compose:     %.1f ns/call (%d iters)\n", dt / N, N);

    /* Integer overflow guard check (Dots #86) + idempotent thread attach/detach */
    double dummyPt[3] = {1.0, 2.0, 3.0};
    CHECK(grassmann_pga3_motor_apply_xyz_batch(m1, dummyPt, SIZE_MAX / 2, dummyPt) == GSIR_ERR_BAD_INPUT,
          "batch pointCount overflow returns GSIR_ERR_BAD_INPUT");
    CHECK(grassmann_attach_thread() == GSIR_OK, "attach_thread idempotent (1)");
    CHECK(grassmann_attach_thread() == GSIR_OK, "attach_thread idempotent (2)");

    /* 1000-pt batch XYZ transform + C-shim memcpy overhead breakdown */
    const size_t PTS = 1000;
    double *inPts = (double *)calloc(PTS * 3, sizeof(double));
    double *outPts = (double *)calloc(PTS * 3, sizeof(double));
    double *tmpPts = (double *)calloc(PTS * 3, sizeof(double));
    for (size_t i = 0; i < PTS * 3; ++i) inPts[i] = (double)i * 0.001;
    const int B = 5000;
    t0 = now_ns();
    for (int i = 0; i < B; ++i) {
      grassmann_pga3_motor_apply_xyz_batch(m1, inPts, PTS, outPts);
    }
    dt = now_ns() - t0;
    double nsPerPt = dt / ((double)B * (double)PTS);
    /* Raw 2x memcpy (input copy + output copy) baseline for shim overhead measurement */
    double tCopy0 = now_ns();
    for (int i = 0; i < B; ++i) {
      memcpy(tmpPts, inPts, PTS * 3 * sizeof(double));
      memcpy(outPts, tmpPts, PTS * 3 * sizeof(double));
    }
    double dtCopy = now_ns() - tCopy0;
    double copyNsPerPt = dtCopy / ((double)B * (double)PTS);
    printf("[bench] pga3_apply_xyz_batch:   %.2f ns/pt (1000 pts in %.2f us; C-shim 2x memcpy baseline=%.2f ns/pt, kernel=%.2f ns/pt)\n",
           nsPerPt, (dt / B) / 1000.0, copyNsPerPt, nsPerPt > copyNsPerPt ? nsPerPt - copyNsPerPt : 0.0);
    free(tmpPts);
    free(inPts);
    free(outPts);

    /* Hot DragHandle GSIR binary frame roundtrip */
    uint64_t sid = grassmann_studio_create();
    uint32_t cap = 262144u, got = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    const char *sta = "{\"op\":\"loadPreset\",\"id\":\"sta_lorentz_boost\"}";
    grassmann_studio_dispatch_json(sid, sta, (uint32_t)strlen(sta), buf, cap, &got);
    uint8_t drag[20] = {0};
    drag[0] = 0x01; /* DragHandle */
    wr_u16(drag + 2, 16);
    wr_u32(drag + 4, 0);
    const int D = 20000;
    t0 = now_ns();
    for (int i = 0; i < D; ++i) {
      wr_f32(drag + 8, (float)(i % 100) * 0.01f);
      grassmann_studio_dispatch_bin(sid, drag, sizeof(drag), buf, cap, &got);
    }
    dt = now_ns() - t0;
    printf("[bench] studio_drag_gsir_frame: %.2f us/frame (%u B/frame, %.0f fps max)\n",
           (dt / D) / 1000.0, got, 1e9 / (dt / D));
    free(buf);
    grassmann_studio_destroy(sid);
  }

  printf("[cabi_smoke] ALL CHECKS PASSED!\n");
  return 0;
}
