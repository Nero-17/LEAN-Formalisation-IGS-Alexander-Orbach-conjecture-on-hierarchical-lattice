import Universality.Percolation.NearCriticalBirthSeries

namespace Universality.Rule
noncomputable section

theorem Classical.supercritical_nearcritical_birth_series_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ neighborhood ≤ radius ∧ 0 < lower ∧ 0 < upper ∧
      ∀ p, critical < p ∧ p < 1 → |p - critical| < neighborhood →
        Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) ≤
          (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) := by
  apply h.birth_series_comparison_from_exit_tail critical hc hc' hfixed order horder
    (fun p => critical < p ∧ p < 1)
  · intro p hp
    exact ⟨hc.trans hp.1, hp.2, ne_of_gt hp.1⟩
  · obtain ⟨neighborhood, hneighborhood, hcritical, hone, hb⟩ :=
      h.actual_supercritical_exit_birth_tail critical hc hc' hfixed order horder
    refine ⟨neighborhood, hneighborhood, hcritical, hone, ?_⟩
    intro radius hradius hradiusSmall
    obtain ⟨constant, hconstant, ht⟩ := hb radius hradius hradiusSmall
    refine ⟨constant, hconstant, ?_⟩
    intro p hp hnear
    exact ht p (hc.trans hp.1) hp.2 hp.1 hnear

theorem Classical.subcritical_nearcritical_birth_series_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ order < rule.edges) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ neighborhood ≤ radius ∧ 0 < lower ∧ 0 < upper ∧
      ∀ p, 0 < p ∧ p < critical → |p - critical| < neighborhood →
        Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) ≤
          (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) := by
  apply h.birth_series_comparison_from_exit_tail critical hc hc' hfixed order horder
    (fun p => 0 < p ∧ p < critical)
  · intro p hp
    exact ⟨hp.1, hp.2.trans hc', ne_of_lt hp.2⟩
  · obtain ⟨neighborhood, hneighborhood, hcritical, hone, hb⟩ :=
      h.actual_subcritical_exit_birth_tail critical hc hc' hfixed order horder hthreshold
    refine ⟨neighborhood, hneighborhood, hcritical, hone, ?_⟩
    intro radius hradius hradiusSmall
    obtain ⟨constant, hconstant, ht⟩ := hb radius hradius hradiusSmall
    refine ⟨constant, hconstant, ?_⟩
    intro p hp hnear
    exact ht p hp.1 (hp.2.trans hc') hp.2 hnear

end
end Universality.Rule
