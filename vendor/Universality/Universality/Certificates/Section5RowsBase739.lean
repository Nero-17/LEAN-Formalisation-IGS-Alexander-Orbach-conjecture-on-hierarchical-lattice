import Universality.Certificates.Section5InputBase739

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_uniform_slacks :
    ∀ zeros ∈ List.range (allocationBase739.depth + 1),
      (allocationBase739.rows[zeros]!).hasUniformSlack allocationBase739.depth zeros
        (allocationBase739.slacks[zeros]!) := by
  apply uniformAllocationRowsCheck_correct allocationBase739 <;> decide +kernel
#check allocationBase739_uniform_slacks

theorem allocationBase739_initial_slacks :
    ∀ zeros ∈ List.range (allocationBase739.depth + 1),
      (allocationBase739.rows[zeros]!).hasSlack allocationBase739.depth zeros
        (allocationBase739.slacks[zeros]!) := by
  intro zeros member
  exact InitialAllocationRow.hasSlack_of_uniform _ _ _ _
    (allocationBase739_uniform_slacks zeros member)

end Universality.Certificates
