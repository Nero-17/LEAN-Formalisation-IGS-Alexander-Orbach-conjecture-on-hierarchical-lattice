import Universality.Graph.SubstitutionConnectivity
import Universality.Examples.GraphMassDimensions

namespace Universality
noncomputable section
open FiniteNetwork Filter
open scoped Topology

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem wheatstone_single_deletion_crosses :
    ∀ edge, wheatstoneNetwork.crosses (onlyClosed edge) = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem oppositeWheatstone_single_deletion_crosses :
    ∀ edge, oppositeWheatstoneNetwork.crosses (onlyClosed edge) = true := by decide

theorem wheatstoneRule_massAdmissible : wheatstoneRule.MassAdmissible where
  connected := ⟨wheatstoneDistanceCertificate.walk⟩
  scale := by
    change 1 < wheatstoneNetwork.fullGraph.dist wheatstoneNetwork.source wheatstoneNetwork.target
    rw [wheatstone_terminal_distance]
    decide
  cut := wheatstone_single_deletion_crosses
  symmetric := wheatstoneRule_terminalSymmetric

theorem oppositeWheatstoneRule_massAdmissible : oppositeWheatstoneRule.MassAdmissible where
  connected := ⟨oppositeWheatstoneDistanceCertificate.walk⟩
  scale := by
    change 1 < oppositeWheatstoneNetwork.fullGraph.dist
      oppositeWheatstoneNetwork.source oppositeWheatstoneNetwork.target
    rw [oppositeWheatstone_terminal_distance]
    decide
  cut := oppositeWheatstone_single_deletion_crosses
  symmetric := oppositeWheatstoneRule_terminalSymmetric

theorem groupedRule_massAdmissible : groupedRule.MassAdmissible :=
  ((wheatstoneRule_massAdmissible.mul wheatstoneRule_massAdmissible).mul
    oppositeWheatstoneRule_massAdmissible).mul oppositeWheatstoneRule_massAdmissible

theorem alternatingRule_massAdmissible : alternatingRule.MassAdmissible :=
  ((wheatstoneRule_massAdmissible.mul oppositeWheatstoneRule_massAdmissible).mul
    wheatstoneRule_massAdmissible).mul oppositeWheatstoneRule_massAdmissible

theorem no_multiplicative_classification_of_admissible_mass_growth {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, observations i (outer * inner) =
      observations i outer * observations i inner) :
    ¬ ∃ classify : (I → T) → ℝ, ∀ rule : Rule,
      rule.MassAdmissible → rule.network.reliability (1 / 2) = 1 / 2 →
      Tendsto (rule.clusterMassGrowth (1 / 2) .connected) atTop
        (𝓝 (classify (fun i => observations i rule))) := by
  rintro ⟨classify, hclassify⟩
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    reordered_graph_cluster_mass_dimensions_differ .connected
  have hg := tendsto_nhds_unique hfirst
    (hclassify groupedRule groupedRule_massAdmissible reordered_rules_fixed_points.1)
  have ha := tendsto_nhds_unique hsecond
    (hclassify alternatingRule alternatingRule_massAdmissible reordered_rules_fixed_points.2)
  apply hne
  rw [hg, ha, reordered_graph_multiplicative_observations observations hmul]

end
end Universality
