import Universality.Percolation.MomentRatioLogRate
import Universality.Analysis.MomentGapProfile

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
attribute [local irreducible] limitingRootSizeMoment

/-- The actual supercritical ratios have one common exponent from some
moment order onward. -/
theorem Classical.supercritical_eventually_root_moment_ratio_common {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∀ᶠ order : ℕ in atTop,
      Tendsto (fun p : ℝ => -(Real.log
        ((rule.limitingRootSizeMoment p (order + 1)).toReal /
          (rule.limitingRootSizeMoment p order).toReal) / Real.log |p - critical|))
        (𝓝[>] critical)
        (𝓝 (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (deriv rule.network.reliability critical))) := by
  have hgrowth : 1 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed
        h.massAdmissible.symmetric h.scale).2.1
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  filter_upwards [eventually_logarithmic_power_gaps_eq
    ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)
    (rule.edges : ℝ) (deriv rule.network.reliability critical) hgrowth hm] with order horder
  have hh := h.supercritical_root_moment_ratio_log_rate critical hc hc' hfixed order
  simpa only [horder] using hh

/-- The common value occurs at every positive order exactly when the
second mass power reaches the volume growth. -/
theorem Classical.supercritical_all_root_moment_gap_coefficients_iff {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    (∀ order : ℕ, 1 ≤ order →
      (max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
          (order + 2) / rule.edges)) 0 -
        max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
          (order + 1) / rule.edges)) 0) / Real.log (deriv rule.network.reliability critical) =
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
        Real.log (deriv rule.network.reliability critical)) ↔
      (rule.edges : ℝ) ≤
        ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 := by
  apply all_logarithmic_power_gaps_eq_iff
  · exact (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed
        h.massAdmissible.symmetric h.scale).2.1
  · exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  · exact rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale


/-- Equivalently, the actual moment-ratio limits all have the common value
precisely in the second-moment mass-growth regime. -/
theorem Classical.supercritical_all_root_moment_gaps_common_iff {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    (∀ order : ℕ, 1 ≤ order →
      Tendsto (fun p : ℝ => -(Real.log
        ((rule.limitingRootSizeMoment p (order + 1)).toReal /
          (rule.limitingRootSizeMoment p order).toReal) / Real.log |p - critical|))
        (𝓝[>] critical)
        (𝓝 (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (deriv rule.network.reliability critical)))) ↔
      (rule.edges : ℝ) ≤
        ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 := by
  rw [← h.supercritical_all_root_moment_gap_coefficients_iff critical hc hc' hfixed]
  constructor
  · intro hall order horder
    exact tendsto_nhds_unique
      (h.supercritical_root_moment_ratio_log_rate critical hc hc' hfixed order)
      (hall order horder)
  · intro hall order horder
    have hh := h.supercritical_root_moment_ratio_log_rate critical hc hc' hfixed order
    simpa only [hall order horder] using hh

end
end Universality.Rule
