import Universality.Certificates.Section5InputBase661

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_packet_checks :
    ∀ packet ∈ allocationBase661.packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = allocationBase661.depth ∧
      (|packet.coefficient| ≤ (allocationBase661.slacks[packet.zeros]! : ℤ) ∨
        packet.capacityChecked allocationBase661.rows) := by
  apply allocationPacketsCheckFast_correct allocationBase661.depth allocationBase661.slacks
    allocationBase661.rows (CorrectionPacket.fastCapacityCheck allocationBase661.rows)
    allocationBase661.packets
  · intro packet _ checked
    exact (CorrectionPacket.fastCapacityCheck_iff allocationBase661.rows packet).mp checked
  · decide +kernel
#check allocationBase661_packet_checks

end Universality.Certificates
