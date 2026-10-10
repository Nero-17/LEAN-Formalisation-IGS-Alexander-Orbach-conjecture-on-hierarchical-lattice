import Universality.Percolation.NearCriticalBirthDomination

namespace Universality.Rule
noncomputable section

theorem Classical.supercritical_nearcritical_birth_domination {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ neighborhood constant : ℝ, 0 < neighborhood ∧ 0 < constant ∧
      ∀ p, critical < p ∧ p < 1 → |p - critical| < neighborhood → ∀ n : ℕ,
        (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1) ≤
          constant * (max
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges)
            ((1 / 2 : ℝ) / rule.edges)) ^ n := by
  apply h.birth_series_domination_from_exit_pointwise critical hc hc' hfixed order horder
    ((1 / 2 : ℝ)) (by norm_num) (fun p => critical < p ∧ p < 1)
  · intro p hp
    exact ⟨hc.trans hp.1, hp.2, ne_of_gt hp.1⟩
  · obtain ⟨neighborhood, hneighborhood, hcritical, hone, hb⟩ :=
      h.actual_supercritical_exit_birth_pointwise critical hc hc' hfixed order horder
    refine ⟨neighborhood, hneighborhood, hcritical, hone, ?_⟩
    intro radius hradius hradiusSmall
    obtain ⟨constant, hconstant, ht⟩ := hb radius hradius hradiusSmall
    refine ⟨constant, hconstant, ?_⟩
    intro p hp hnear j
    simpa only [pow_mul] using ht p (hc.trans hp.1) hp.2 hp.1 hnear j

theorem Classical.subcritical_nearcritical_birth_domination {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ neighborhood constant : ℝ, 0 < neighborhood ∧ 0 < constant ∧
      ∀ p, 0 < p ∧ p < critical → |p - critical| < neighborhood → ∀ n : ℕ,
        (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1) ≤
          constant * (max
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges)
            ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ order / rule.edges)) ^ n := by
  apply h.birth_series_domination_from_exit_pointwise critical hc hc' hfixed order horder
    ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ order) (pow_nonneg (Nat.cast_nonneg _) _) (fun p => 0 < p ∧ p < critical)
  · intro p hp
    exact ⟨hp.1, hp.2.trans hc', ne_of_lt hp.2⟩
  · obtain ⟨neighborhood, hneighborhood, hcritical, hone, hb⟩ :=
      h.actual_subcritical_exit_birth_pointwise critical hc hc' hfixed order horder
    refine ⟨neighborhood, hneighborhood, hcritical, hone, ?_⟩
    intro radius hradius hradiusSmall
    obtain ⟨constant, hconstant, ht⟩ := hb radius hradius hradiusSmall
    refine ⟨constant, hconstant, ?_⟩
    intro p hp hnear j
    simpa only [pow_mul] using ht p hp.1 (hp.2.trans hc') hp.2 hnear j

end
end Universality.Rule
