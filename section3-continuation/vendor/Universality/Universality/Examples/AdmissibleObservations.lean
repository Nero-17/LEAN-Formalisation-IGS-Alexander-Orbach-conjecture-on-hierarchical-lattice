import Universality.Examples.AdmissibleMassCounterexample

namespace Universality
noncomputable section
open FiniteNetwork Filter
open scoped Topology

/-- Multiplicativity is required only on the admissible domain, not on every
finite network. Full classical admissibility remains a separate obligation. -/
theorem reordered_admissible_multiplicative_observations {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, outer.MassAdmissible → inner.MassAdmissible →
      observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => observations i groupedRule) = (fun i => observations i alternatingRule) := by
  have hfirst := wheatstoneRule_massAdmissible
  have hsecond := oppositeWheatstoneRule_massAdmissible
  funext i
  dsimp only [groupedRule, alternatingRule]
  rw [hmul i _ _ ((hfirst.mul hfirst).mul hsecond) hsecond,
    hmul i _ _ (hfirst.mul hfirst) hsecond, hmul i _ _ hfirst hfirst,
    hmul i _ _ ((hfirst.mul hsecond).mul hfirst) hsecond,
    hmul i _ _ (hfirst.mul hsecond) hfirst, hmul i _ _ hfirst hsecond]
  ac_rfl

theorem no_classification_by_admissible_multiplicative_observations
    {I T : Type*} [CommMonoid T] (observations : I → Rule → T)
    (hmul : ∀ i outer inner, outer.MassAdmissible → inner.MassAdmissible →
      observations i (outer * inner) = observations i outer * observations i inner) :
    ¬ ∃ classify : (I → T) → ℝ, ∀ rule : Rule,
      rule.MassAdmissible → rule.network.reliability (1 / 2) = 1 / 2 →
      Tendsto (rule.clusterMassGrowth (1 / 2) .connected) atTop
        (𝓝 (classify (fun i => observations i rule))) := by
  rintro ⟨classify, hclassify⟩
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    reordered_graph_cluster_mass_dimensions_differ .connected
  have hgrouped := tendsto_nhds_unique hfirst
    (hclassify groupedRule groupedRule_massAdmissible reordered_rules_fixed_points.1)
  have halternating := tendsto_nhds_unique hsecond
    (hclassify alternatingRule alternatingRule_massAdmissible reordered_rules_fixed_points.2)
  apply hne
  rw [hgrouped, halternating, reordered_admissible_multiplicative_observations observations hmul]

end
end Universality
