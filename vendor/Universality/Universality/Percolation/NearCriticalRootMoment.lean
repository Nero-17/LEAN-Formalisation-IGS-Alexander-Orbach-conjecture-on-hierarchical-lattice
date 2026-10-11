import Universality.Percolation.ActualBirthSeriesComparison
import Universality.Percolation.RealAnnealedMoment

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 0

/-- Add the genuine initial birth level and normalize to the actual
uniform-root moment. The geometric sum now has exactly the paper's range
from one through the first exit depth. -/
theorem Classical.root_moment_comparison_from_birth_series {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1 ∧ p ≠ critical)
    (hseries :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ neighborhood ≤ radius ∧ 0 < lower ∧ 0 < upper ∧
      ∀ p, allowed p → |p - critical| < neighborhood →
        Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)) ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ n) ≤
          (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)) ∧
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)) ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ n)) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ 0 < lower ∧ 0 < upper ∧ ∀ p, allowed p → |p - critical| < neighborhood →
        rule.limitingRootSizeMoment p order ≠ ⊤ ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) ≤
          (rule.limitingRootSizeMoment p order).toReal ∧
        (rule.limitingRootSizeMoment p order).toReal ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) := by
  obtain ⟨radius, near, lower, upper, hradius, hradiusCritical, hradiusOne,
    hnear, hnearRadius, hlower, hupper, hb⟩ := hseries
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans hm
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  let factor : ℝ := ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)
  have hfactor : 0 < factor := div_pos (sub_pos.mpr hm) (sub_pos.mpr hv)
  let ratio : ℝ := ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges
  have hspectral : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hratio : 0 < ratio := div_pos (pow_pos hspectral _) hmpos
  let initialBound : ℝ := (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower critical (order + 1) 0 + 1
  have hinitial : 0 < initialBound := add_pos_of_nonneg_of_pos
    (mul_nonneg (one_div_nonneg.mpr hmpos.le) (rule.expectedClusterBirthPower_nonneg hc.le hc'.le _ _)) zero_lt_one
  have hcontinuous : Continuous (fun p : ℝ => (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0) :=
    continuous_const.mul (rule.continuous_expectedClusterBirthPower (order + 1) 0)
  have hlocal : ∀ᶠ p in 𝓝 critical,
      (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 < initialBound :=
    hcontinuous.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨initialRadius, hinitialRadius, hinitialBound⟩ := Metric.eventually_nhds_iff.mp hlocal
  refine ⟨radius, min near initialRadius, factor * lower / ratio, factor * (initialBound + upper) / ratio,
    hradius, hradiusCritical, hradiusOne, lt_min hnear hinitialRadius,
    div_pos (mul_pos hfactor hlower) hratio, div_pos (mul_pos hfactor (add_pos hinitial hupper)) hratio, ?_⟩
  intro p hpAllowed hpNear
  obtain ⟨hp, hp', hpne⟩ := hallowed p hpAllowed
  have hpoint := hb p hpAllowed (hpNear.trans_le (min_le_left _ _))
  have hs : Summable (fun generation : ℕ => (1 / (rule.edges : ℝ)) ^ (generation + 1) *
      rule.expectedClusterBirthPower p (order + 1) generation) := by
    apply (summable_nat_add_iff 1).mp
    exact hpoint.1
  have hfinite := (rule.limitingRootSizeMoment_finite_iff_birth_summable
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le order).mpr hs
  have hreal := rule.limitingRootSizeMoment_toReal_birth_series
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le order hfinite
  rw [hs.tsum_eq_zero_add] at hreal
  simp only [zero_add, pow_one] at hreal
  change (rule.limitingRootSizeMoment p order).toReal = factor *
    ((1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 +
      ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)) at hreal
  have hdepth := h.reliability_exit_pos critical radius p hc hc' hfixed hradiusCritical hradiusOne
    hp hp' hpne ((hpNear.trans_le (min_le_left _ _)).trans_le hnearRadius)
  have hsumOne : (1 : ℝ) ≤ ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n := by
    have hh := Finset.single_le_sum (fun n _ => (pow_pos hratio n).le)
      (Finset.mem_range.mpr hdepth)
    simpa only [pow_zero] using hh
  have hsumShift : (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ (n + 1)) =
      ratio * ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n := by
    simp only [pow_succ', Finset.mul_sum]
  have hzeroNonneg : 0 ≤ (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 :=
    mul_nonneg (one_div_nonneg.mpr hmpos.le) (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
  have hzeroBound := (hinitialBound (y := p)
    (by simpa only [Real.dist_eq] using hpNear.trans_le (min_le_right _ _))).le
  refine ⟨hfinite, ?_, ?_⟩
  · change (factor * lower / ratio) *
      (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ (n + 1)) ≤ _
    rw [hsumShift, hreal]
    have hh := mul_le_mul_of_nonneg_left
      (hpoint.2.1.trans (le_add_of_nonneg_left hzeroNonneg)) hfactor.le
    calc
      _ = factor * (lower * ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n) := by field_simp [hratio.ne'] <;> ring
      _ ≤ _ := hh
  · change _ ≤ (factor * (initialBound + upper) / ratio) *
      (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ (n + 1))
    rw [hsumShift, hreal]
    have hconstant := mul_le_mul_of_nonneg_left hsumOne hinitial.le
    have hinside : (1 / (rule.edges : ℝ)) * rule.expectedClusterBirthPower p (order + 1) 0 +
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p (order + 1) (n + 1)) ≤
        (initialBound + upper) * ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n := by
      have hbound := hpoint.2.2
      change _ ≤ upper * ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n at hbound
      nlinarith only [hconstant, hzeroBound, hbound]
    calc
      _ ≤ factor * ((initialBound + upper) * ∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p), ratio ^ n) :=
        mul_le_mul_of_nonneg_left hinside hfactor.le
      _ = _ := by field_simp [hratio.ne'] <;> ring

theorem Classical.supercritical_nearcritical_root_moment_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ 0 < lower ∧ 0 < upper ∧ ∀ p, critical < p ∧ p < 1 → |p - critical| < neighborhood →
        rule.limitingRootSizeMoment p order ≠ ⊤ ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) ≤
          (rule.limitingRootSizeMoment p order).toReal ∧
        (rule.limitingRootSizeMoment p order).toReal ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) := by
  apply h.root_moment_comparison_from_birth_series critical hc hc' hfixed order
    (fun p => critical < p ∧ p < 1)
  · intro p hp
    exact ⟨hc.trans hp.1, hp.2, ne_of_gt hp.1⟩
  · exact h.supercritical_nearcritical_birth_series_comparison critical hc hc' hfixed (order + 1) (by omega)

theorem Classical.subcritical_nearcritical_root_moment_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) < rule.edges) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ 0 < lower ∧ 0 < upper ∧ ∀ p, 0 < p ∧ p < critical → |p - critical| < neighborhood →
        rule.limitingRootSizeMoment p order ≠ ⊤ ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) ≤
          (rule.limitingRootSizeMoment p order).toReal ∧
        (rule.limitingRootSizeMoment p order).toReal ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges) ^ (n + 1)) := by
  apply h.root_moment_comparison_from_birth_series critical hc hc' hfixed order
    (fun p => 0 < p ∧ p < critical)
  · intro p hp
    exact ⟨hp.1, hp.2.trans hc', ne_of_lt hp.2⟩
  · exact h.subcritical_nearcritical_birth_series_comparison critical hc hc' hfixed (order + 1) (by omega) hthreshold

end
end Universality.Rule
