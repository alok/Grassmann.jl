#define _POSIX_C_SOURCE 200809L

#include "grassmann/cabi.h"

#include <math.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define CHECK_STATUS(call)                                                     \
  do {                                                                         \
    grassmann_status_v1 status_ = (call);                                      \
    if (status_ != GRASSMANN_OK_V1) {                                          \
      fprintf(stderr, "%s failed with status %d\n", #call, (int)status_);     \
      return EXIT_FAILURE;                                                     \
    }                                                                          \
  } while (0)

static int approximately(double actual, double expected, double tolerance) {
  return fabs(actual - expected) <= tolerance;
}

static int coordinates_match(
    const double actual[3],
    const double expected[3],
    double tolerance) {
  return approximately(actual[0], expected[0], tolerance) &&
    approximately(actual[1], expected[1], tolerance) &&
    approximately(actual[2], expected[2], tolerance);
}

static int extract_coordinates(
    const grassmann_pga3_point_v1 *point,
    double out[3]) {
  grassmann_status_v1 status = grassmann_pga3_extract_point_v1(point, out);
  if (status != GRASSMANN_OK_V1) {
    fprintf(stderr, "point extraction failed with status %d\n", (int)status);
    return 0;
  }
  return 1;
}

static int rotation_matches(
    double axis_x,
    double axis_y,
    double axis_z,
    const double source[3],
    const double expected[3],
    double angle,
    double tolerance) {
  grassmann_pga3_motor_v1 rotor;
  grassmann_pga3_point_v1 point;
  grassmann_pga3_point_v1 rotated;
  double actual[3];

  return grassmann_pga3_make_rotor_v1(
           axis_x, axis_y, axis_z, angle, &rotor) == GRASSMANN_OK_V1 &&
    grassmann_pga3_make_point_v1(
      source[0], source[1], source[2], &point) == GRASSMANN_OK_V1 &&
    grassmann_pga3_motor_apply_point_v1(
      &rotor, &point, &rotated) == GRASSMANN_OK_V1 &&
    extract_coordinates(&rotated, actual) &&
    coordinates_match(actual, expected, tolerance);
}

static double elapsed_nanoseconds(
    const struct timespec *start,
    const struct timespec *end) {
  return (double)(end->tv_sec - start->tv_sec) * 1e9 +
    (double)(end->tv_nsec - start->tv_nsec);
}

typedef struct worker_result {
  grassmann_status_v1 initialize_status;
  grassmann_status_v1 make_point_status;
  grassmann_status_v1 extract_status;
  grassmann_status_v1 finalize_status;
  double xyz[3];
} worker_result;

static void *run_worker_smoke(void *opaque) {
  worker_result *result = (worker_result *)opaque;
  grassmann_pga3_point_v1 point;

  result->initialize_status = grassmann_thread_initialize_v1();
  if (result->initialize_status != GRASSMANN_OK_V1) {
    return NULL;
  }

  result->make_point_status =
    grassmann_pga3_make_point_v1(7.0, 8.0, 9.0, &point);
  if (result->make_point_status == GRASSMANN_OK_V1) {
    result->extract_status = grassmann_pga3_extract_point_v1(
      &point, result->xyz);
  }
  result->finalize_status = grassmann_thread_finalize_v1();
  return NULL;
}

int main(void) {
  const double tolerance = 1e-8;

  if (grassmann_cabi_version_v1() != GRASSMANN_CABI_VERSION_V1) {
    fprintf(stderr, "unexpected Grassmann C ABI version\n");
    return EXIT_FAILURE;
  }

  if (grassmann_pga3_make_point_v1(0.0, 0.0, 0.0, NULL) !=
      GRASSMANN_NULL_POINTER_V1) {
    fprintf(stderr, "null-output guard failed\n");
    return EXIT_FAILURE;
  }

  grassmann_pga3_point_v1 preinit_point;
  if (grassmann_pga3_make_point_v1(0.0, 0.0, 0.0, &preinit_point) !=
      GRASSMANN_NOT_INITIALIZED_V1 ||
      grassmann_thread_initialize_v1() != GRASSMANN_NOT_INITIALIZED_V1) {
    fprintf(stderr, "pre-initialization guard failed\n");
    return EXIT_FAILURE;
  }

  CHECK_STATUS(grassmann_initialize_v1());
  CHECK_STATUS(grassmann_initialize_v1());

  worker_result worker = {
    GRASSMANN_INIT_FAILED_V1,
    GRASSMANN_INIT_FAILED_V1,
    GRASSMANN_INIT_FAILED_V1,
    GRASSMANN_INIT_FAILED_V1,
    {0.0, 0.0, 0.0}
  };
  pthread_t worker_thread;
  if (pthread_create(&worker_thread, NULL, run_worker_smoke, &worker) != 0 ||
      pthread_join(worker_thread, NULL) != 0) {
    fprintf(stderr, "foreign worker thread could not be run\n");
    return EXIT_FAILURE;
  }
  const double worker_expected[3] = {7.0, 8.0, 9.0};
  if (worker.initialize_status != GRASSMANN_OK_V1 ||
      worker.make_point_status != GRASSMANN_OK_V1 ||
      worker.extract_status != GRASSMANN_OK_V1 ||
      worker.finalize_status != GRASSMANN_OK_V1 ||
      !coordinates_match(worker.xyz, worker_expected, tolerance)) {
    fprintf(stderr, "foreign worker thread ABI check failed\n");
    return EXIT_FAILURE;
  }

  const double quarter_turn = acos(-1.0) / 2.0;
  const double axis_x[3] = {1.0, 0.0, 0.0};
  const double axis_y[3] = {0.0, 1.0, 0.0};
  const double axis_z[3] = {0.0, 0.0, 1.0};
  if (!rotation_matches(
        1.0, 0.0, 0.0, axis_y, axis_z, quarter_turn, tolerance) ||
      !rotation_matches(
        0.0, 1.0, 0.0, axis_z, axis_x, quarter_turn, tolerance) ||
      !rotation_matches(
        0.0, 0.0, 1.0, axis_x, axis_y, quarter_turn, tolerance)) {
    fprintf(stderr, "right-handed quarter-turn convention check failed\n");
    return EXIT_FAILURE;
  }

  grassmann_pga3_point_v1 point;
  grassmann_pga3_motor_v1 translator;
  grassmann_pga3_point_v1 translated_point;
  double translated_xyz[3];
  const double translated_expected[3] = {5.0, 0.0, 3.5};
  const double point_coeff_expected[8] = {0.0, 0.0, 0.0, 1.0,
                                          0.0, 3.0, 2.0, 1.0};
  const double translator_coeff_expected[8] = {1.0, 0.0, 0.0, 0.0,
                                               -2.0, -1.0, -0.25, 0.0};

  CHECK_STATUS(grassmann_pga3_make_point_v1(1.0, 2.0, 3.0, &point));
  CHECK_STATUS(grassmann_pga3_make_translator_v1(4.0, -2.0, 0.5, &translator));
  for (size_t i = 0; i < 8; ++i) {
    if (!approximately(point.coeff[i], point_coeff_expected[i], tolerance) ||
        !approximately(
          translator.coeff[i], translator_coeff_expected[i], tolerance)) {
      fprintf(stderr, "documented packed layout mismatch at %zu\n", i);
      return EXIT_FAILURE;
    }
  }
  CHECK_STATUS(grassmann_pga3_motor_apply_point_v1(
    &translator, &point, &translated_point));
  if (!extract_coordinates(&translated_point, translated_xyz) ||
      !coordinates_match(translated_xyz, translated_expected, tolerance)) {
    fprintf(stderr,
      "translation mismatch: got [%.17g, %.17g, %.17g]\n",
      translated_xyz[0], translated_xyz[1], translated_xyz[2]);
    return EXIT_FAILURE;
  }

  grassmann_pga3_motor_v1 rotor;
  grassmann_pga3_motor_v1 reversed_rotor;
  grassmann_pga3_motor_v1 rotor_identity;
  CHECK_STATUS(grassmann_pga3_make_rotor_v1(0.0, 0.0, 1.0, 0.5, &rotor));
  CHECK_STATUS(grassmann_pga3_motor_reverse_v1(&rotor, &reversed_rotor));
  CHECK_STATUS(grassmann_pga3_motor_compose_v1(
    &rotor, &reversed_rotor, &rotor_identity));

  if (!approximately(
        rotor_identity.coeff[GRASSMANN_PGA3_MOTOR_SCALAR_V1], 1.0, tolerance)) {
    fprintf(stderr, "rotor/reverse composition has non-unit scalar\n");
    return EXIT_FAILURE;
  }
  for (size_t i = 1; i < 8; ++i) {
    if (!approximately(rotor_identity.coeff[i], 0.0, tolerance)) {
      fprintf(stderr, "rotor/reverse composition is not identity at %zu\n", i);
      return EXIT_FAILURE;
    }
  }

  grassmann_pga3_motor_v1 composed;
  grassmann_pga3_point_v1 rotated_point;
  grassmann_pga3_point_v1 sequential_point;
  grassmann_pga3_point_v1 composed_point;
  double sequential_xyz[3];
  double composed_xyz[3];

  CHECK_STATUS(grassmann_pga3_motor_compose_v1(
    &translator, &rotor, &composed));
  CHECK_STATUS(grassmann_pga3_motor_apply_point_v1(
    &rotor, &point, &rotated_point));
  CHECK_STATUS(grassmann_pga3_motor_apply_point_v1(
    &translator, &rotated_point, &sequential_point));
  CHECK_STATUS(grassmann_pga3_motor_apply_point_v1(
    &composed, &point, &composed_point));

  if (!extract_coordinates(&sequential_point, sequential_xyz) ||
      !extract_coordinates(&composed_point, composed_xyz) ||
      !coordinates_match(composed_xyz, sequential_xyz, tolerance)) {
    fprintf(stderr,
      "composition mismatch: sequential [%.17g, %.17g, %.17g], "
      "composed [%.17g, %.17g, %.17g]\n",
      sequential_xyz[0], sequential_xyz[1], sequential_xyz[2],
      composed_xyz[0], composed_xyz[1], composed_xyz[2]);
    return EXIT_FAILURE;
  }

  enum { rc_stress_iterations = 100000, timing_iterations = 10000 };
  struct timespec started;
  struct timespec stopped;
  grassmann_pga3_motor_v1 stress_motor;
  grassmann_pga3_motor_v1 stress_reversed;
  grassmann_pga3_point_v1 stress_point;
  double stress_xyz[3];

  if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) {
    fprintf(stderr, "monotonic clock is unavailable\n");
    return EXIT_FAILURE;
  }
  for (int i = 0; i < rc_stress_iterations; ++i) {
    CHECK_STATUS(grassmann_pga3_motor_compose_v1(
      &translator, &rotor, &stress_motor));
    CHECK_STATUS(grassmann_pga3_motor_reverse_v1(
      &stress_motor, &stress_reversed));
    CHECK_STATUS(grassmann_pga3_motor_reverse_v1(
      &stress_reversed, &stress_motor));
    CHECK_STATUS(grassmann_pga3_motor_apply_point_v1(
      &stress_motor, &point, &stress_point));
    CHECK_STATUS(grassmann_pga3_extract_point_v1(&stress_point, stress_xyz));
  }
  if (clock_gettime(CLOCK_MONOTONIC, &stopped) != 0 ||
      !coordinates_match(stress_xyz, composed_xyz, tolerance)) {
    fprintf(stderr, "repeated-call ownership stress failed\n");
    return EXIT_FAILURE;
  }
  const double rc_stress_ns = elapsed_nanoseconds(&started, &stopped);

  if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) {
    fprintf(stderr, "monotonic clock is unavailable\n");
    return EXIT_FAILURE;
  }
  for (int i = 0; i < timing_iterations; ++i) {
    CHECK_STATUS(grassmann_pga3_make_point_v1(1.0, 2.0, 3.0, &point));
  }
  if (clock_gettime(CLOCK_MONOTONIC, &stopped) != 0) {
    fprintf(stderr, "monotonic clock is unavailable\n");
    return EXIT_FAILURE;
  }
  const double make_point_ns =
    elapsed_nanoseconds(&started, &stopped) / timing_iterations;

  if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) {
    fprintf(stderr, "monotonic clock is unavailable\n");
    return EXIT_FAILURE;
  }
  for (int i = 0; i < timing_iterations; ++i) {
    CHECK_STATUS(grassmann_pga3_extract_point_v1(&point, composed_xyz));
  }
  if (clock_gettime(CLOCK_MONOTONIC, &stopped) != 0) {
    fprintf(stderr, "monotonic clock is unavailable\n");
    return EXIT_FAILURE;
  }
  const double extract_point_ns =
    elapsed_nanoseconds(&started, &stopped) / timing_iterations;

  printf(
    "Grassmann C ABI v%u.%u smoke test passed; translated point "
    "[%.6f, %.6f, %.6f]\n",
    grassmann_cabi_version_v1() >> 16,
    grassmann_cabi_version_v1() & UINT32_C(0xffff),
    translated_xyz[0], translated_xyz[1], translated_xyz[2]);
  printf(
    "Informational C ABI boundary timing (%d iterations, no threshold): "
    "construct/result copy %.1f ns/call; packed input/extract/result copy "
    "%.1f ns/call\n",
    timing_iterations, make_point_ns, extract_point_ns);
  printf(
    "Ownership stress passed: %d iterations / %d consuming calls in %.1f ms\n",
    rc_stress_iterations, rc_stress_iterations * 5, rc_stress_ns / 1e6);
  return EXIT_SUCCESS;
}
