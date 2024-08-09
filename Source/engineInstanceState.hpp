#ifndef BOSSNONADAPTIVEENGINE_OPERATORSTATS_H
#define BOSSNONADAPTIVEENGINE_OPERATORSTATS_H

#include <cstdint>

namespace nonadaptive {

class EngineInstanceState {
public:
  EngineInstanceState() : vectorizedDOP(-1) {}

  void setVectorizedDOP(int32_t vectorizedDOP_) { vectorizedDOP = vectorizedDOP_; }
  [[nodiscard]] int32_t getVectorizedDOP() const { return vectorizedDOP; }

private:
  int32_t vectorizedDOP;
};

} // namespace adaptive

#endif // BOSSNONADAPTIVEENGINE_OPERATORSTATS_H
