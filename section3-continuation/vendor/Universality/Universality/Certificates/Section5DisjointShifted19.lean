import Universality.Certificates.Section5InputShifted19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_disjoint :
    allocationShifted19.packets.Pairwise
      (fun packet other => packet.signature ≠ other.signature) := by
  apply packets_pairwise_of_consecutive
  decide +kernel
#check allocationShifted19_disjoint

end Universality.Certificates
