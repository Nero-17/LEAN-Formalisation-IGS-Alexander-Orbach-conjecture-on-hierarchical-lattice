import Universality.Certificates.Section5InputShifted19

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_uniform_slacks :
    ∀ zeros ∈ List.range (allocationShifted19.depth + 1),
      (allocationShifted19.rows[zeros]!).hasUniformSlack allocationShifted19.depth zeros
        (allocationShifted19.slacks[zeros]!) := by
  apply uniformAllocationRowsCheck_correct allocationShifted19 <;> decide +kernel
#check allocationShifted19_uniform_slacks

theorem allocationShifted19_initial_slacks :
    ∀ zeros ∈ List.range (allocationShifted19.depth + 1),
      (allocationShifted19.rows[zeros]!).hasSlack allocationShifted19.depth zeros
        (allocationShifted19.slacks[zeros]!) := by
  intro zeros member
  exact InitialAllocationRow.hasSlack_of_uniform _ _ _ _
    (allocationShifted19_uniform_slacks zeros member)

end Universality.Certificates
