import Universality.Certificates.Section5MassRepairDataBase661

namespace Universality.Certificates.MassRepairChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem checked16 : correctionsMassEvaluation packets16 = value16 := by
  decide +kernel

#print axioms checked16
theorem checked17 : correctionsMassEvaluation packets17 = value17 := by
  decide +kernel

#print axioms checked17
theorem checked18 : correctionsMassEvaluation packets18 = value18 := by
  decide +kernel

#print axioms checked18
theorem checked19 : correctionsMassEvaluation packets19 = value19 := by
  decide +kernel

#print axioms checked19

end Universality.Certificates.MassRepairChunksBase661
