import Universality.Certificates.Section5GroupsBase739
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_length :
    2 ^ 952 + allocationBase739.allocation (List.replicate 952 false) =
      739 ^ 100 + 0 := by
  exact allocationBase739.length_certificate allocationBase739_capacityValid 739 0
    (by decide +kernel)

end Universality.Certificates
