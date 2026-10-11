import Universality.Certificates.Section5InputBase661

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_uniform_slacks :
    ∀ zeros ∈ List.range (allocationBase661.depth + 1),
      (allocationBase661.rows[zeros]!).hasUniformSlack allocationBase661.depth zeros
        (allocationBase661.slacks[zeros]!) := by
  apply uniformAllocationRowsCheck_correct allocationBase661 <;> decide +kernel
#check allocationBase661_uniform_slacks

theorem allocationBase661_initial_slacks :
    ∀ zeros ∈ List.range (allocationBase661.depth + 1),
      (allocationBase661.rows[zeros]!).hasSlack allocationBase661.depth zeros
        (allocationBase661.slacks[zeros]!) := by
  intro zeros member
  exact InitialAllocationRow.hasSlack_of_uniform _ _ _ _
    (allocationBase661_uniform_slacks zeros member)

end Universality.Certificates
