import Universality.Certificates.Section5CountsBase739

namespace Universality.Certificates

def allocationBase739Moments : AllocationMomentCertificate where
  allocation := allocationBase739
  moments := certificateBase739
  allCounts := allocationBase739AllCounts
  firstCounts := allocationBase739FirstCounts

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_groups_checked : allocationBase739Moments.groupChecked := by
  apply AllocationMomentCertificate.groupChecked_of_linear <;> decide +kernel
#check allocationBase739_groups_checked

end Universality.Certificates
