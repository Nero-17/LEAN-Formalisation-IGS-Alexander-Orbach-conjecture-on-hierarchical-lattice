import Universality.Certificates.Section5InputBase661

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_disjoint :
    allocationBase661.packets.Pairwise
      (fun packet other => packet.signature ≠ other.signature) := by
  apply packets_pairwise_of_consecutive
  decide +kernel
#check allocationBase661_disjoint

end Universality.Certificates
