import Universality.Section5.SeedShifted19
import Universality.Section5.PhysicalExponents

/-! The actual infinite-cluster probability threshold of the shifted graph. -/

namespace Universality.Section5
noncomputable section

theorem certifiedRuleShifted19_physical_infinite_cluster_positive_iff
    (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty certifiedRuleShifted19.network.InteriorVertex := exactAllocationShifted19.interior_nonempty
    letI : NeZero certifiedRuleShifted19.edges := exactAllocationShifted19.edges_neZero
    0 < certifiedRuleShifted19.physicalInfiniteClusterProbability
      certifiedRuleShifted19_classical.edges_gt_one p ↔ 1 / 2 < p :=
  exactAllocationShifted19.physical_infinite_cluster_positive_iff p nonnegative at_most_one

end
end Universality.Section5
