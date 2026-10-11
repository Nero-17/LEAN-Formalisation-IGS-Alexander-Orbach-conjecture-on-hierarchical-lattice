import Universality.Certificates.Section5CountsBase19

namespace Universality.Certificates

def allocationBase19Moments : AllocationMomentCertificate where
  allocation := allocationBase19
  moments := certificateBase19
  allCounts := allocationBase19AllCounts
  firstCounts := allocationBase19FirstCounts

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase19_groups_checked : allocationBase19Moments.groupChecked := by
  apply AllocationMomentCertificate.groupChecked_of_linear <;> decide +kernel
#check allocationBase19_groups_checked

end Universality.Certificates
