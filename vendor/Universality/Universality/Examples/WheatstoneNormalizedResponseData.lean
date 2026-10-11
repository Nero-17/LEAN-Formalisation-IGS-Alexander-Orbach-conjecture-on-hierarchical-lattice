import Universality.Examples.WheatstoneCriticalCoefficient

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology

def wheatstoneNormalizedThirdResponse (p : Icc (1 / 2 : ℝ) 1) : ℝ :=
  -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension p /
    ((p : ℝ) - 1/2) ^ (Real.log 5 / Real.log (13/8) - 3)

def wheatstoneNormalizedThirdForcing (p : Icc (1 / 2 : ℝ) 1) : ℝ :=
  (-wheatstoneThirdForcing p / 5) /
    ((p : ℝ) - 1/2) ^ (Real.log 5 / Real.log (13/8) - 3)

theorem wheatstone_normalized_third_equation (p : Icc (1 / 2 : ℝ) 1) :
    wheatstoneNormalizedThirdResponse p =
      wheatstoneCriticalNormalizedCoefficient p * wheatstoneNormalizedThirdResponse (wheatstoneHalfIteration p) +
        wheatstoneNormalizedThirdForcing p := by
  by_cases hp : p = wheatstoneHalfCenter
  · subst p
    rw [wheatstone_half_iteration_fixed]
    simp only [wheatstoneNormalizedThirdResponse, wheatstoneNormalizedThirdForcing,
      wheatstoneHalfCenter, Subtype.coe_mk, sub_self, div_zero, mul_zero, add_zero,
      Real.zero_rpow wheatstone_response_order_bounds.1.ne']
  · exact power_normalized_affine_equation wheatstoneHalfIteration
      (fun q => -iteratedDeriv 3 wheatstoneNetwork.clusterNumberAnalyticExtension q)
      (fun q => wheatstoneRealCrossing.derivative.eval (q : ℝ) ^ 3 / 5)
      (fun q => -wheatstoneThirdForcing q / 5) (fun q => (q : ℝ) - 1/2)
      (fun q => wheatstoneRealSecant.eval (q : ℝ)) _ p
      (wheatstone_half_deviation_positive p hp) (wheatstone_real_secant_pos p p.property)
      (wheatstone_real_secant_identity p) (wheatstone_half_response_equation p)

theorem wheatstone_normalized_third_forcing_bound :
    ∃ bound : ℝ, 0 < bound ∧ ∀ᶠ p : Icc (1/2 : ℝ) 1 in 𝓝 wheatstoneHalfCenter,
      0 ≤ wheatstoneNormalizedThirdForcing p ∧
      wheatstoneNormalizedThirdForcing p ≤ bound * ((p : ℝ) - 1/2) ^
        (1 - (Real.log 5 / Real.log (13/8) - 3)) := by
  have hmap : Tendsto (fun p : Icc (1/2 : ℝ) 1 => (p : ℝ))
      (𝓝 wheatstoneHalfCenter) (𝓝 (1/2 : ℝ)) := continuous_subtype_val.continuousAt.tendsto
  obtain ⟨bound, hbound, hb⟩ := (wheatstone_third_forcing_isBigO.comp_tendsto hmap).exists_pos
  refine ⟨bound / 5, by positivity, ?_⟩
  filter_upwards [hb.bound] with p hp
  have hnonnegative : 0 ≤ (p : ℝ) - 1/2 := sub_nonneg.mpr p.property.1
  have hforcing : wheatstoneThirdForcing p ≤ 0 := by
    have hh := wheatstone_third_forcing_bound p p.property
    linarith
  have hp' : -wheatstoneThirdForcing p ≤ bound * ((p : ℝ) - 1/2) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonpos hforcing, abs_of_nonneg hnonnegative] using hp
  constructor
  · unfold wheatstoneNormalizedThirdForcing
    exact div_nonneg (div_nonneg (neg_nonneg.mpr hforcing) (by norm_num)) (Real.rpow_nonneg hnonnegative _)
  · by_cases hzero : (p : ℝ) - 1/2 = 0
    · simp only [wheatstoneNormalizedThirdForcing, hzero,
        Real.zero_rpow wheatstone_response_order_bounds.1.ne',
        Real.zero_rpow (sub_pos.mpr wheatstone_response_order_bounds.2).ne', div_zero, mul_zero, le_refl]
    · have hpositive : 0 < (p : ℝ) - 1/2 := lt_of_le_of_ne hnonnegative (Ne.symm hzero)
      unfold wheatstoneNormalizedThirdForcing
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hpositive _)).mpr
      have hproduct : ((bound / 5) * ((p : ℝ) - 1/2) ^ (1 - (Real.log 5 / Real.log (13/8) - 3))) *
          ((p : ℝ) - 1/2) ^ (Real.log 5 / Real.log (13/8) - 3) = (bound / 5) * ((p : ℝ) - 1/2) := by
        rw [mul_assoc, ← Real.rpow_add hpositive]
        simp only [sub_add_cancel, Real.rpow_one]
      rw [hproduct]
      linarith

end
end Universality
