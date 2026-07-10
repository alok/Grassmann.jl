#include "grassmann/cabi.h"

#include <type_traits>

static_assert(std::is_standard_layout_v<grassmann_pga3_motor_v1>);
static_assert(std::is_trivially_copyable_v<grassmann_pga3_motor_v1>);
static_assert(std::is_standard_layout_v<grassmann_pga3_point_v1>);
static_assert(std::is_trivially_copyable_v<grassmann_pga3_point_v1>);
static_assert(GRASSMANN_CABI_VERSION_V1 == UINT32_C(0x00010001));
static_assert(GRASSMANN_BAD_LENGTH_V1 != GRASSMANN_INVALID_MOTOR_V1);

using motor_is_unit_signature = grassmann_status_v1 (*)(
  const grassmann_pga3_motor_v1 *, double, int *);
using motor_unary_signature = grassmann_status_v1 (*)(
  const grassmann_pga3_motor_v1 *, grassmann_pga3_motor_v1 *);
using motor_batch_signature = grassmann_status_v1 (*)(
  const grassmann_pga3_motor_v1 *, const double *, size_t, double *);

static_assert(std::is_same_v<
  decltype(&grassmann_pga3_motor_is_unit_v1), motor_is_unit_signature>);
static_assert(std::is_same_v<
  decltype(&grassmann_pga3_motor_normalize_v1), motor_unary_signature>);
static_assert(std::is_same_v<
  decltype(&grassmann_pga3_motor_inverse_v1), motor_unary_signature>);
static_assert(std::is_same_v<
  decltype(&grassmann_pga3_motor_apply_xyz_batch_v1),
  motor_batch_signature>);

int main() {
  grassmann_pga3_motor_v1 motor{};
  grassmann_pga3_point_v1 point{};
  return motor.coeff[GRASSMANN_PGA3_MOTOR_SCALAR_V1] == 0.0 &&
      point.coeff[GRASSMANN_PGA3_POINT_WEIGHT_V1] == 0.0
    ? 0
    : 1;
}
