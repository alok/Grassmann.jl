#include "grassmann/cabi.h"

#include <type_traits>

static_assert(std::is_standard_layout_v<grassmann_pga3_motor_v1>);
static_assert(std::is_trivially_copyable_v<grassmann_pga3_motor_v1>);
static_assert(std::is_standard_layout_v<grassmann_pga3_point_v1>);
static_assert(std::is_trivially_copyable_v<grassmann_pga3_point_v1>);

int main() {
  grassmann_pga3_motor_v1 motor{};
  grassmann_pga3_point_v1 point{};
  return motor.coeff[GRASSMANN_PGA3_MOTOR_SCALAR_V1] == 0.0 &&
      point.coeff[GRASSMANN_PGA3_POINT_WEIGHT_V1] == 0.0
    ? 0
    : 1;
}
