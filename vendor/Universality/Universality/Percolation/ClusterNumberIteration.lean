import Universality.Percolation.ClusterNumberBoundary
import Universality.Graph.Iteration

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open FiniteNetwork

/-- Exact finite-volume cluster-number series, including the terminal
correction. It is derived from actual percolation configurations. -/
theorem generation_expectedClusterNumber (rule : Rule) (n : ℕ) (p : ℝ) :
    (rule.generation n).network.expectedClusterNumber p =
      (∑ k ∈ Finset.range (n + 1), (rule.edges : ℝ) ^ (n - k) *
        rule.network.expectedInternalClusterNumber (rule.network.reliability^[k] p)) +
        2 - rule.network.reliability^[n + 1] p := by
  induction n generalizing p with
  | zero =>
    simpa [generation] using rule.network.expectedClusterNumber_boundary_correction p
  | succ n ih =>
    change ((rule.generation n).network.substitute rule.network).expectedClusterNumber p = _
    rw [FiniteNetwork.expectedClusterNumber_substitute, ih, generation_edges, Nat.cast_pow]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, Function.iterate_zero, id_eq,
      Function.iterate_succ_apply]
    ring

end
end Universality.Rule
