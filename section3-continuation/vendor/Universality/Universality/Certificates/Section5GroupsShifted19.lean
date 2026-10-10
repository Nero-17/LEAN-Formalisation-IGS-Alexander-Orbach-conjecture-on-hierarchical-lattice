import Universality.Certificates.Section5CountsShifted19

namespace Universality.Certificates

def allocationShifted19Moments : AllocationMomentCertificate where
  allocation := allocationShifted19
  moments := certificateShifted19
  allCounts := allocationShifted19AllCounts
  firstCounts := allocationShifted19FirstCounts

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_groups_checked : allocationShifted19Moments.groupChecked := by
  apply AllocationMomentCertificate.groupChecked_of_linear <;> decide +kernel
#check allocationShifted19_groups_checked

end Universality.Certificates
