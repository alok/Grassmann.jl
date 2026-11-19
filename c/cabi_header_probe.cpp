#include "grassmann/cabi.h"

static_assert(GRASSMANN_CABI_VERSION == 0x00020000u, "unexpected CABI version");
static_assert(GSIR_OK == 0, "unexpected GSIR_OK");
static_assert(GSIR_ERR_BUF_SMALL == -3, "unexpected GSIR_ERR_BUF_SMALL");

int grassmann_cpp_header_probe(void) {
  return (int)grassmann_cabi_version();
}
