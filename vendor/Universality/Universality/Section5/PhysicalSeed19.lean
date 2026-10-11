import Universality.Section5.Seed19
import Universality.Section5.PhysicalExponents

/-! Actual physical observables of the fully certified base-19 graph. -/

namespace Universality.Section5
noncomputable section

theorem certifiedRule19_hasCriticalExponents :
    letI : Nonempty certifiedRule19.network.InteriorVertex := certifiedRule19_responses.interior_nonempty
    letI : NeZero certifiedRule19.edges := certifiedRule19_responses.edges_neZero
    certifiedRule19.HasCriticalExponents certifiedRule19_responses.classical.edges_gt_one
      (1 / 2) (13 / 70) (10 / 7) (219 / 13) (-3 / 50) :=
  certifiedRule19_responses.hasCriticalExponents (by norm_num)

theorem certifiedRule19_physical_infinite_cluster_positive_iff
    (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty certifiedRule19.network.InteriorVertex := certifiedRule19_responses.interior_nonempty
    letI : NeZero certifiedRule19.edges := certifiedRule19_responses.edges_neZero
    0 < certifiedRule19.physicalInfiniteClusterProbability
      certifiedRule19_responses.classical.edges_gt_one p ↔ 1 / 2 < p :=
  certifiedRule19_responses.physical_infinite_cluster_positive_iff p nonnegative at_most_one

end
end Universality.Section5
