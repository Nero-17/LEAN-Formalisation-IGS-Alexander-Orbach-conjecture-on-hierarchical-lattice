import Universality.Certificates.Section5GroupsShifted19
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_length :
    2 ^ 424 + allocationShifted19.allocation (List.replicate 424 false) =
      19 ^ 100 + 480 := by
  exact allocationShifted19.length_certificate allocationShifted19_capacityValid 19 480
    (by decide +kernel)

end Universality.Certificates
