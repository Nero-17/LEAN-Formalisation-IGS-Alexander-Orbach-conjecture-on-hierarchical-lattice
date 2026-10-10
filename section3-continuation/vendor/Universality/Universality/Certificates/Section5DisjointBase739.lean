import Universality.Certificates.Section5InputBase739

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_disjoint :
    allocationBase739.packets.Pairwise
      (fun packet other => packet.signature ≠ other.signature) := by
  apply packets_pairwise_of_consecutive
  decide +kernel
#check allocationBase739_disjoint

end Universality.Certificates
