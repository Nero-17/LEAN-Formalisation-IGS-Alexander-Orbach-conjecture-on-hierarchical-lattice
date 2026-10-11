import Universality.Certificates.Section5MassRepairDataBase661

namespace Universality.Certificates.MassRepairChunksBase661

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

theorem parts_checked : chunks.flatten = allocationBase661.packets := by
  decide +kernel

theorem baseline_checked : baselineMassEvaluation 936 = baseline := by
  decide +kernel

theorem total_checked :
    addIntegerMassPairs
      (addIntegerMassPairs baseline
        ((allocationBase661RepairInitialMass.1 : ℤ), (allocationBase661RepairInitialMass.2 : ℤ)))
      (sumIntegerMassPairs values) = massCertificateValue 936 661 := by
  decide +kernel

#print axioms parts_checked
#print axioms baseline_checked
#print axioms total_checked
end Universality.Certificates.MassRepairChunksBase661
