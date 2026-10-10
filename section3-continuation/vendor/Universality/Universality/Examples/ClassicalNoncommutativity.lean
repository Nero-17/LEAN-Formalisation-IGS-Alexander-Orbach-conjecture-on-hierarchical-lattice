import Universality.Graph.ClassicalSubstitution
import Universality.Examples.ClassicalSeeds

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem groupedRule_classical : groupedRule.Classical :=
  ((wheatstoneRule_classical.mul wheatstoneRule_classical).mul
    oppositeWheatstoneRule_classical).mul oppositeWheatstoneRule_classical

theorem alternatingRule_classical : alternatingRule.Classical :=
  ((wheatstoneRule_classical.mul oppositeWheatstoneRule_classical).mul
    wheatstoneRule_classical).mul oppositeWheatstoneRule_classical

/-- Multiplicativity is assumed only when the rules and their composite are
classical. No extension to inadmissible networks is required. -/
theorem reordered_classical_multiplicative_observations {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, outer.Classical → inner.Classical → (outer * inner).Classical →
      observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => observations i groupedRule) = (fun i => observations i alternatingRule) := by
  have hfirst := wheatstoneRule_classical
  have hsecond := oppositeWheatstoneRule_classical
  have hproduct i outer inner (ho : outer.Classical) (hi : inner.Classical) := hmul i outer inner ho hi (ho.mul hi)
  funext i
  dsimp only [groupedRule, alternatingRule]
  rw [hproduct i _ _ ((hfirst.mul hfirst).mul hsecond) hsecond,
    hproduct i _ _ (hfirst.mul hfirst) hsecond, hproduct i _ _ hfirst hfirst,
    hproduct i _ _ ((hfirst.mul hsecond).mul hfirst) hsecond,
    hproduct i _ _ (hfirst.mul hsecond) hfirst, hproduct i _ _ hfirst hsecond]
  ac_rfl

theorem no_classification_by_classical_multiplicative_observations
    {I T : Type*} [CommMonoid T] (observations : I → Rule → T)
    (hmul : ∀ i outer inner, outer.Classical → inner.Classical → (outer * inner).Classical →
      observations i (outer * inner) = observations i outer * observations i inner) :
    ¬ ∃ classify : (I → T) → ℝ, ∀ rule : Rule,
      rule.Classical → rule.network.reliability (1 / 2) = 1 / 2 →
      Tendsto (rule.clusterMassGrowth (1 / 2) .connected) atTop
        (𝓝 (classify (fun i => observations i rule))) := by
  rintro ⟨classify, hclassify⟩
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    reordered_graph_cluster_mass_dimensions_differ .connected
  have hgrouped := tendsto_nhds_unique hfirst
    (hclassify groupedRule groupedRule_classical reordered_rules_fixed_points.1)
  have halternating := tendsto_nhds_unique hsecond
    (hclassify alternatingRule alternatingRule_classical reordered_rules_fixed_points.2)
  apply hne
  rw [hgrouped, halternating, reordered_classical_multiplicative_observations observations hmul]

theorem reordered_classical_multiplicative_dimensions
    {I : Type*} (observations : I → Rule → ℝ)
    (hmul : ∀ i outer inner, outer.Classical → inner.Classical → (outer * inner).Classical →
      observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => Real.log (observations i groupedRule) /
      Real.log (groupedRule.network.fullGraph.dist groupedRule.network.source groupedRule.network.target)) =
    (fun i => Real.log (observations i alternatingRule) /
      Real.log (alternatingRule.network.fullGraph.dist alternatingRule.network.source alternatingRule.network.target)) := by
  have hobservation := reordered_classical_multiplicative_observations observations hmul
  funext i
  rw [congrFun hobservation i, reordered_rules_terminal_distances.1, reordered_rules_terminal_distances.2]

end
end Universality
