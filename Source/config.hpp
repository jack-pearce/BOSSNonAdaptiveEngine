#ifndef BOSSNONADAPTIVEENGINE_CONFIG_HPP
#define BOSSNONADAPTIVEENGINE_CONFIG_HPP

#include <cstdint>

namespace nonadaptive::config {

// NOLINTBEGIN
extern int32_t nonVectorizedDOP;
extern int minPartitionSize;
// NOLINTEND

extern const int32_t LOGICAL_CORE_COUNT;

} // namespace nonadaptive::config

#endif // BOSSNONADAPTIVEENGINE_CONFIG_HPP
