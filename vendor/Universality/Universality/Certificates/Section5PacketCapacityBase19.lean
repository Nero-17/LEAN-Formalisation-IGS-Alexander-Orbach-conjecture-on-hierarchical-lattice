import Universality.Certificates.Section5InputBase19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase19_packet_checks :
    ∀ packet ∈ allocationBase19.packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = allocationBase19.depth ∧
      (|packet.coefficient| ≤ (allocationBase19.slacks[packet.zeros]! : ℤ) ∨
        packet.capacityChecked allocationBase19.rows) := by
  apply allocationPacketsCheckFast_correct allocationBase19.depth allocationBase19.slacks
    allocationBase19.rows (CorrectionPacket.fastCapacityCheck allocationBase19.rows)
    allocationBase19.packets
  · intro packet _ checked
    exact (CorrectionPacket.fastCapacityCheck_iff allocationBase19.rows packet).mp checked
  · decide +kernel
#check allocationBase19_packet_checks

end Universality.Certificates
