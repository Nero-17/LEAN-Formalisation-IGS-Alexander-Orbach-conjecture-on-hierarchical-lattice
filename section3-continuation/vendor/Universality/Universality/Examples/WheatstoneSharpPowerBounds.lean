import Universality.Analysis.CompactCriticalResponse
import Universality.Examples.WheatstoneNormalizedResponseData

namespace Universality
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology

theorem wheatstone_normalized_third_response_bounds :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ p : Icc (1/2 : ℝ) 1,
      p ≠ wheatstoneHalfCenter → lower ≤ wheatstoneNormalizedThirdResponse p ∧
        wheatstoneNormalizedThirdResponse p ≤ upper := by
  have hmap : Tendsto (fun p : Icc (1/2 : ℝ) 1 => (p : ℝ))
      (𝓝 wheatstoneHalfCenter) (𝓝 (1/2 : ℝ)) := continuous_subtype_val.continuousAt.tendsto
  obtain ⟨rate, hrate, hrateBound⟩ := wheatstone_critical_normalized_coefficient_exp_bound
  obtain ⟨bound, hbound, hforcing⟩ := wheatstone_normalized_third_forcing_bound
  apply bounded_positive_normalized_response_of_compact_escape wheatstoneHalfIteration
    wheatstoneNormalizedThirdResponse (fun p => wheatstoneCriticalNormalizedCoefficient p)
    wheatstoneNormalizedThirdForcing (fun p => (p : ℝ) - 1/2)
    wheatstoneHalfCenter (1/4) (3/2) rate bound (1 - (Real.log 5 / Real.log (13/8) - 3))
    (by norm_num) (by norm_num) hrate hbound.le
    (sub_pos.mpr wheatstone_response_order_bounds.2) wheatstone_half_iteration_escape
  · apply wheatstone_half_response_continuous.continuousOn.div
      ((continuous_subtype_val.sub continuous_const).continuousOn.rpow_const
        (fun _ _ => Or.inr wheatstone_response_order_bounds.1.le))
    intro p hp
    exact (Real.rpow_pos_of_pos (wheatstone_half_deviation_positive p
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp)) _).ne'
  · intro p
    exact div_nonneg (neg_nonneg.mpr (wheatstone_cluster_number_third_deriv_nonpos p p.property))
      (Real.rpow_nonneg (sub_nonneg.mpr p.property.1) _)
  · intro p hp
    exact div_pos (neg_pos.mpr (wheatstone_cluster_number_third_deriv_neg p
      (sub_pos.mp (wheatstone_half_deviation_positive p hp)) p.property.2))
      (Real.rpow_pos_of_pos (wheatstone_half_deviation_positive p hp) _)
  · exact (continuous_subtype_val.sub continuous_const).continuousOn
  · intro p
    exact sub_nonneg.mpr p.property.1
  · exact Eventually.of_forall wheatstone_normalized_third_equation
  · filter_upwards [hmap.eventually hrateBound] with p hp
    exact ⟨wheatstone_critical_normalized_coefficient_le_one p p.property,
      by simpa only [abs_of_nonneg (sub_nonneg.mpr p.property.1)] using hp⟩
  · have hsecant : ∀ᶠ p : Icc (1/2 : ℝ) 1 in 𝓝 wheatstoneHalfCenter,
        (3/2 : ℝ) ≤ wheatstoneRealSecant.eval (p : ℝ) :=
      (wheatstone_half_polynomial_continuous wheatstoneRealSecant).continuousAt.eventually
        (le_mem_nhds (by change (3/2 : ℝ) < wheatstoneRealSecant.eval (1/2); rw [wheatstone_real_secant_half]; norm_num))
    filter_upwards [hsecant] with p hp
    change (3/2 : ℝ) * ((p : ℝ) - 1/2) ≤ wheatstoneRealCrossing.eval (p : ℝ) - 1/2
    rw [wheatstone_real_secant_identity]
    nlinarith [mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr p.property.1)]
  · exact hforcing

theorem wheatstone_half_third_response_power_bounds :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ p : ℝ, 1/2 < p → p ≤ 1 →
      lower * (p - 1/2) ^ (Real.log 5 / Real.log (13/8) - 3) ≤
        -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ∧
      -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p ≤
        upper * (p - 1/2) ^ (Real.log 5 / Real.log (13/8) - 3) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := wheatstone_normalized_third_response_bounds
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro p hp hp'
  have hneq : (⟨p, hp.le, hp'⟩ : Icc (1/2 : ℝ) 1) ≠ wheatstoneHalfCenter := by
    intro hh
    have hv := congrArg Subtype.val hh
    change p = (1/2 : ℝ) at hv
    linarith
  have hh := hbounds ⟨p, hp.le, hp'⟩ hneq
  have hpositive := Real.rpow_pos_of_pos (sub_pos.mpr hp) (Real.log 5 / Real.log (13/8) - 3)
  exact ⟨(le_div_iff₀ hpositive).mp hh.1, (div_le_iff₀ hpositive).mp hh.2⟩

end
end Universality
