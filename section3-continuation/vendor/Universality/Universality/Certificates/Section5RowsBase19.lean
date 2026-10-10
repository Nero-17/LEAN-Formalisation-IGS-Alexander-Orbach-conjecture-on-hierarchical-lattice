import Universality.Certificates.Section5InputBase19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase19_uniform_slacks :
    ∀ zeros ∈ List.range (allocationBase19.depth + 1),
      (allocationBase19.rows[zeros]!).hasUniformSlack allocationBase19.depth zeros
        (allocationBase19.slacks[zeros]!) := by
  apply uniformAllocationRowsCheck_correct allocationBase19 <;> decide +kernel
#check allocationBase19_uniform_slacks

theorem allocationBase19_initial_slacks :
    ∀ zeros ∈ List.range (allocationBase19.depth + 1),
      (allocationBase19.rows[zeros]!).hasSlack allocationBase19.depth zeros
        (allocationBase19.slacks[zeros]!) := by
  intro zeros member
  exact InitialAllocationRow.hasSlack_of_uniform _ _ _ _
    (allocationBase19_uniform_slacks zeros member)

end Universality.Certificates
