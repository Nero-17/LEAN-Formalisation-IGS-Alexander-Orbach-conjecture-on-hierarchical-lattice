import Universality.Certificates.Section5MassRepairDataBase661

namespace Universality.Certificates.MassRepairChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem checked20 : correctionsMassEvaluation packets20 = value20 := by
  decide +kernel

#print axioms checked20
theorem checked21 : correctionsMassEvaluation packets21 = value21 := by
  decide +kernel

#print axioms checked21
theorem checked22 : correctionsMassEvaluation packets22 = value22 := by
  decide +kernel

#print axioms checked22
theorem checked23 : correctionsMassEvaluation packets23 = value23 := by
  decide +kernel

#print axioms checked23

end Universality.Certificates.MassRepairChunksBase661
