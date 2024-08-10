#include "config.hpp"

namespace nonadaptive::config {

// NOLINTBEGIN
int32_t nonVectorizedDOP = 1;
int minPartitionSize = 300'000;
// NOLINTEND

// TODO - machine config, these should be determined and set during the build process
const int32_t LOGICAL_CORE_COUNT = 4;
// const int32_t LOGICAL_CORE_COUNT = 10;

} // namespace nonadaptive::config
