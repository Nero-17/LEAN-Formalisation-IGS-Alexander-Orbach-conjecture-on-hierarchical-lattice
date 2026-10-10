import Universality.Certificates.Section5MassRepairDataBase739

namespace Universality.Certificates.MassRepairChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem checked00 : correctionsMassEvaluation packets00 = value00 := by
  decide +kernel

#print axioms checked00
theorem checked01 : correctionsMassEvaluation packets01 = value01 := by
  decide +kernel

#print axioms checked01
theorem checked02 : correctionsMassEvaluation packets02 = value02 := by
  decide +kernel

#print axioms checked02
theorem checked03 : correctionsMassEvaluation packets03 = value03 := by
  decide +kernel

#print axioms checked03

end Universality.Certificates.MassRepairChunksBase739
