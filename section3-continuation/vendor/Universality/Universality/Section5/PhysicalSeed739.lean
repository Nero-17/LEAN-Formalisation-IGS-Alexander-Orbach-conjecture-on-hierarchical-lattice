import Universality.Section5.Seed739
import Universality.Section5.PhysicalSeed19
import Universality.Section5.TranscendentalDimensions

/-! Actual observable exponents and the independent 19/739 counterexample.
This module has no dependency on the concrete base-661 mass certificate. -/

namespace Universality.Section5
noncomputable section

theorem certifiedRule739_hasCriticalExponents :
    letI : Nonempty certifiedRule739.network.InteriorVertex := certifiedRule739_responses.interior_nonempty
    letI : NeZero certifiedRule739.edges := certifiedRule739_responses.edges_neZero
    certifiedRule739.HasCriticalExponents certifiedRule739_responses.classical.edges_gt_one
      (1 / 2) (13 / 70) (10 / 7) (219 / 13) (-3 / 50) :=
  certifiedRule739_responses.hasCriticalExponents (by norm_num)

theorem certifiedRule19_and739_sameCriticalExponentUniversalityClass :
    letI : Nonempty certifiedRule19.network.InteriorVertex := certifiedRule19_responses.interior_nonempty
    letI : NeZero certifiedRule19.edges := certifiedRule19_responses.edges_neZero
    letI : Nonempty certifiedRule739.network.InteriorVertex := certifiedRule739_responses.interior_nonempty
    letI : NeZero certifiedRule739.edges := certifiedRule739_responses.edges_neZero
    Rule.SameCriticalExponentUniversalityClass certifiedRule19 certifiedRule739
      certifiedRule19_responses.classical.edges_gt_one certifiedRule739_responses.classical.edges_gt_one
      (1 / 2) (1 / 2) :=
  certifiedRule19_responses.sameCriticalExponentUniversalityClass certifiedRule739_responses
    (by norm_num) (by norm_num)

theorem certifiedRule739_physical_infinite_cluster_positive_iff
    (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty certifiedRule739.network.InteriorVertex := certifiedRule739_responses.interior_nonempty
    letI : NeZero certifiedRule739.edges := certifiedRule739_responses.edges_neZero
    0 < certifiedRule739.physicalInfiniteClusterProbability
      certifiedRule739_responses.classical.edges_gt_one p ↔ 1 / 2 < p :=
  certifiedRule739_responses.physical_infinite_cluster_positive_iff p nonnegative at_most_one

theorem certifiedRule19_and739_scale_incommensurate :
    ¬ ScaleCommensurate
      (certifiedRule19.network.fullGraph.dist certifiedRule19.network.source certifiedRule19.network.target)
      (certifiedRule739.network.fullGraph.dist certifiedRule739.network.source certifiedRule739.network.target) := by
  rw [certifiedRule19_responses.distance, certifiedRule739_responses.distance]
  exact coprime_not_commensurate
    (one_lt_pow₀ (by decide : 1 < (19 : ℕ)) (by decide : (100 : ℕ) ≠ 0))
    (((by decide : Nat.Coprime 19 739).pow_left 100).pow_right 100)

end
end Universality.Section5
