import Universality.Percolation.PreexitMomentBounds
import Universality.Percolation.AnnealedBirthFirstMoment

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem bernoulli_mixing_local_comparison (critical distortion : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hd : 1 < distortion) :
    ∀ᶠ q in 𝓝 critical,
      q ≤ distortion * critical ∧ critical ≤ distortion * q ∧
      1 - q ≤ distortion * (1 - critical) ∧ 1 - critical ≤ distortion * (1 - q) := by
  have hfirst : critical < distortion * critical := by nlinarith
  have hsecond : 1 - critical < distortion * (1 - critical) := by nlinarith
  have hleft : ∀ᶠ q in 𝓝 critical, q < distortion * critical := gt_mem_nhds hfirst
  have hright : ∀ᶠ q in 𝓝 critical, critical < distortion * q :=
    (show ContinuousAt (fun q : ℝ => distortion * q) critical by fun_prop).eventually (lt_mem_nhds hfirst)
  have hleft' : ∀ᶠ q in 𝓝 critical, 1 - q < distortion * (1 - critical) :=
    (show ContinuousAt (fun q : ℝ => 1 - q) critical by fun_prop).eventually (gt_mem_nhds hsecond)
  have hright' : ∀ᶠ q in 𝓝 critical, 1 - critical < distortion * (1 - q) :=
    (show ContinuousAt (fun q : ℝ => distortion * (1 - q)) critical by fun_prop).eventually (lt_mem_nhds hsecond)
  filter_upwards [hleft, hright, hleft', hright'] with q h1 h2 h3 h4
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

namespace Rule
open FiniteNetwork

theorem Classical.preexit_boundary_mean_comparison {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (distortion : ℝ) (hd : 1 < distortion) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
      (∀ j ≤ n + 1, |rule.network.reliability^[j] p - critical| < radius) →
        (rule.generation n).network.expectedInternalBoundaryMass p ≤
          distortion ^ 2 * (rule.generation n).network.expectedInternalBoundaryMass critical ∧
        (rule.generation n).network.expectedInternalBoundaryMass critical ≤
          distortion ^ 2 * (rule.generation n).network.expectedInternalBoundaryMass p := by
  obtain ⟨momentRadius, hmomentRadius, hmoment⟩ := h.preexit_moment_comparison_with_distortion critical hc hc' hfixed distortion hd
  obtain ⟨mixRadius, hmixRadius, hmix⟩ := Metric.eventually_nhds_iff.mp
    (bernoulli_mixing_local_comparison critical distortion hc hc' hd)
  refine ⟨min momentRadius mixRadius, lt_min hmomentRadius hmixRadius, ?_⟩
  intro p hp hp' n horbit
  have hconditional (state : LiveState) := hmoment p hp hp' n
    (fun j hj => (horbit j (by omega)).trans_le (min_le_left _ _)) state 1
  simp only [conditionalVertexMoment_one, pow_one] at hconditional
  have hqpos := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr ((h.generation n).connected _)
  have hqless := (rule.generation n).network.reliability_lt_one hp hp'
  have hqclose : |(rule.generation n).network.reliability p - critical| < mixRadius := by
    rw [rule.generation_reliability_iterate]
    exact (horbit (n + 1) le_rfl).trans_le (min_le_right _ _)
  have hmixing := hmix (y := (rule.generation n).network.reliability p) (by simpa only [Real.dist_eq] using hqclose)
  rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate p hqpos hqless,
    (rule.generation n).network.expectedInternalBoundaryMass_disintegrate critical
      (by rwa [rule.generation_fixed_point critical hfixed]) (by rwa [rule.generation_fixed_point critical hfixed]),
    rule.generation_fixed_point critical hfixed]
  have hnonneg (parameter : ℝ) (hparam : 0 ≤ parameter) (hparam' : parameter ≤ 1) (state : LiveState) :
      0 ≤ (rule.generation n).network.conditionalVertexMass parameter state :=
    (rule.generation n).network.conditionalInternalMean_nonneg parameter hparam hparam' _ _ _
  constructor
  · have hfirst := mul_le_mul hmixing.1 (hconditional .connected).1
      (hnonneg p hp.le hp'.le .connected) (mul_nonneg (zero_lt_one.trans hd).le hc.le)
    have hsecond := mul_le_mul hmixing.2.2.1 (hconditional .both).1
      (hnonneg p hp.le hp'.le .both) (mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hc'.le))
    nlinarith
  · have hfirst := mul_le_mul hmixing.2.1 (hconditional .connected).2
      (hnonneg critical hc.le hc'.le .connected) (mul_nonneg (zero_lt_one.trans hd).le hqpos.le)
    have hsecond := mul_le_mul hmixing.2.2.2 (hconditional .both).2
      (hnonneg critical hc.le hc'.le .both) (mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hqless.le))
    nlinarith

end Rule
end
end Universality
