import Universality.Examples.WheatstoneSharpPowerBounds
import Universality.Examples.WheatstoneRawAlpha

namespace Universality
noncomputable section
set_option maxHeartbeats 700000
open Set Filter
open scoped Topology

theorem wheatstone_third_response_two_sided_power_bounds :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 → p ≠ 1/2 →
      lower * |p - 1/2| ^ (Real.log 5 / Real.log (13/8) - 3) ≤
        |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| ∧
      |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| ≤
        upper * |p - 1/2| ^ (Real.log 5 / Real.log (13/8) - 3) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := wheatstone_half_third_response_power_bounds
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro p hp hpneq
  by_cases hright : 1/2 < p
  · have hh := hbounds p hright hp.2.le
    simpa only [abs_of_pos (sub_pos.mpr hright),
      abs_of_neg (wheatstone_cluster_number_third_deriv_neg p hright hp.2.le)] using hh
  · have hleft : p < 1/2 := lt_of_le_of_ne (le_of_not_gt hright) hpneq
    have hother : 1/2 < 1-p := by linarith
    have hotherOne : 1-p ≤ 1 := by linarith [hp.1]
    have hh := hbounds (1-p) hother hotherOne
    have hreflection := wheatstone_cluster_number_third_derivative_reflection p hp
    have habsolute : |iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p| =
        -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1-p) := by
      have heq : iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p =
          -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension (1-p) := by linarith
      rw [heq, abs_neg, abs_of_neg (wheatstone_cluster_number_third_deriv_neg (1-p) hother hotherOne)]
    rw [habsolute, abs_of_neg (sub_neg.mpr hleft)]
    have hdeviation : -(p - 1/2) = (1-p) - 1/2 := by ring
    rw [hdeviation]
    exact hh

end
end Universality
