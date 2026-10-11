import Universality.Certificates.Section5InputShifted19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_packet_checks :
    ∀ packet ∈ allocationShifted19.packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = allocationShifted19.depth ∧
      (|packet.coefficient| ≤ (allocationShifted19.slacks[packet.zeros]! : ℤ) ∨
        packet.capacityChecked allocationShifted19.rows) := by
  apply allocationPacketsCheckFast_correct allocationShifted19.depth allocationShifted19.slacks
    allocationShifted19.rows (CorrectionPacket.fastCapacityCheck allocationShifted19.rows)
    allocationShifted19.packets
  · intro packet _ checked
    exact (CorrectionPacket.fastCapacityCheck_iff allocationShifted19.rows packet).mp checked
  · decide +kernel
#check allocationShifted19_packet_checks

end Universality.Certificates
