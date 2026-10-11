import Universality.Certificates.Section5CountsBase661

namespace Universality.Certificates

def allocationBase661Moments : AllocationMomentCertificate where
  allocation := allocationBase661
  moments := certificateBase661
  allCounts := allocationBase661AllCounts
  firstCounts := allocationBase661FirstCounts

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_groups_checked : allocationBase661Moments.groupChecked := by
  apply AllocationMomentCertificate.groupChecked_of_linear <;> decide +kernel
#check allocationBase661_groups_checked

end Universality.Certificates
