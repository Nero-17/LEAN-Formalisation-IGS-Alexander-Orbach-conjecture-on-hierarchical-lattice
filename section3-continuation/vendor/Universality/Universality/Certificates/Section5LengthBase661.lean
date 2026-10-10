import Universality.Certificates.Section5GroupsBase661
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_length :
    2 ^ 936 + allocationBase661.allocation (List.replicate 936 false) =
      661 ^ 100 + 0 := by
  exact allocationBase661.length_certificate allocationBase661_capacityValid 661 0
    (by decide +kernel)

end Universality.Certificates
