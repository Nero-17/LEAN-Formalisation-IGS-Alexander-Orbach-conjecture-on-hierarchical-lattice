import Universality.Certificates.Section5MassRepairDataBase739

namespace Universality.Certificates.MassRepairChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem checked04 : correctionsMassEvaluation packets04 = value04 := by
  decide +kernel

#print axioms checked04
theorem checked05 : correctionsMassEvaluation packets05 = value05 := by
  decide +kernel

#print axioms checked05
theorem checked06 : correctionsMassEvaluation packets06 = value06 := by
  decide +kernel

#print axioms checked06
theorem checked07 : correctionsMassEvaluation packets07 = value07 := by
  decide +kernel

#print axioms checked07

end Universality.Certificates.MassRepairChunksBase739
