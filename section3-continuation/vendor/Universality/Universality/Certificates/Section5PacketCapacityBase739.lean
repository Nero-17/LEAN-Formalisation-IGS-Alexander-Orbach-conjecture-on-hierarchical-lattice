import Universality.Certificates.Section5InputBase739

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_packet_checks :
    ∀ packet ∈ allocationBase739.packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = allocationBase739.depth ∧
      (|packet.coefficient| ≤ (allocationBase739.slacks[packet.zeros]! : ℤ) ∨
        packet.capacityChecked allocationBase739.rows) := by
  apply allocationPacketsCheckFast_correct allocationBase739.depth allocationBase739.slacks
    allocationBase739.rows (CorrectionPacket.fastCapacityCheck allocationBase739.rows)
    allocationBase739.packets
  · intro packet _ checked
    exact (CorrectionPacket.fastCapacityCheck_iff allocationBase739.rows packet).mp checked
  · decide +kernel
#check allocationBase739_packet_checks

end Universality.Certificates
