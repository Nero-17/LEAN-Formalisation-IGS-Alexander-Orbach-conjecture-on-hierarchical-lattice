import Universality.Certificates.Section5MassRepairDataBase739

namespace Universality.Certificates.MassRepairChunksBase739

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem parts_checked : chunks.flatten = allocationBase739.packets := by
  decide +kernel

theorem baseline_checked : baselineMassEvaluation 952 = baseline := by
  decide +kernel

theorem total_checked :
    addIntegerMassPairs
      (addIntegerMassPairs baseline
        ((allocationBase739RepairInitialMass.1 : ℤ), (allocationBase739RepairInitialMass.2 : ℤ)))
      (sumIntegerMassPairs values) = massCertificateValue 952 739 := by
  decide +kernel

#print axioms parts_checked
#print axioms baseline_checked
#print axioms total_checked
end Universality.Certificates.MassRepairChunksBase739
