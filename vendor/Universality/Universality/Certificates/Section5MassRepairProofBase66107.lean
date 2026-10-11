import Universality.Certificates.Section5MassRepairDataBase661

namespace Universality.Certificates.MassRepairChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem checked28 : correctionsMassEvaluation packets28 = value28 := by
  decide +kernel

#print axioms checked28
theorem checked29 : correctionsMassEvaluation packets29 = value29 := by
  decide +kernel

#print axioms checked29

end Universality.Certificates.MassRepairChunksBase661
