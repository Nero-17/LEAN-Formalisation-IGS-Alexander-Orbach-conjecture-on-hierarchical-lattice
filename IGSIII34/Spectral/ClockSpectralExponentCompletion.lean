import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII34.Spectral
noncomputable section

theorem clock_spectral_exponent_interval_completion
    (radius resistance : ℝ) (radiusAboveOne : 1 < radius) (resistanceAboveOne : 1 < resistance) :
    0 < Real.log radius / Real.log (radius * resistance) ∧
      Real.log radius / Real.log (radius * resistance) < 1 := by
  have radiusPositive := zero_lt_one.trans radiusAboveOne
  have resistancePositive := zero_lt_one.trans resistanceAboveOne
  have clockAboveOne : 1 < radius * resistance := by nlinarith [mul_pos (sub_pos.mpr radiusAboveOne) (sub_pos.mpr resistanceAboveOne)]
  have clockLogPositive := Real.log_pos clockAboveOne
  refine ⟨div_pos (Real.log_pos radiusAboveOne) clockLogPositive, (div_lt_one clockLogPositive).mpr ?_⟩
  rw [Real.log_mul radiusPositive.ne' resistancePositive.ne']
  linarith [Real.log_pos resistanceAboveOne]

theorem clock_spectral_exponent_difference_completion
    (radius resistance : ℝ) (radiusAboveOne : 1 < radius) (resistanceAboveOne : 1 < resistance) :
    Real.log radius / Real.log (radius * resistance) - 1 =
      -Real.log resistance / Real.log (radius * resistance) := by
  have radiusPositive := zero_lt_one.trans radiusAboveOne
  have resistancePositive := zero_lt_one.trans resistanceAboveOne
  have clockAboveOne : 1 < radius * resistance := by nlinarith [mul_pos (sub_pos.mpr radiusAboveOne) (sub_pos.mpr resistanceAboveOne)]
  have clockLogPositive := Real.log_pos clockAboveOne
  have logarithm := Real.log_mul radiusPositive.ne' resistancePositive.ne'
  field_simp [clockLogPositive.ne']
  linarith

theorem clock_resistance_exponent_identity_completion
    (radius resistance : ℝ) (radiusAboveOne : 1 < radius) (resistanceAboveOne : 1 < resistance) :
    (radius * resistance)^(-Real.log resistance / Real.log (radius * resistance)) = resistance⁻¹ := by
  have resistancePositive := zero_lt_one.trans resistanceAboveOne
  have clockAboveOne : 1 < radius * resistance := by nlinarith [mul_pos (sub_pos.mpr radiusAboveOne) (sub_pos.mpr resistanceAboveOne)]
  have clockPositive := zero_lt_one.trans clockAboveOne
  have clockLogPositive := Real.log_pos clockAboveOne
  rw [Real.rpow_def_of_pos clockPositive]
  have logarithmIdentity : Real.log (radius * resistance) * (-Real.log resistance / Real.log (radius * resistance)) =
      -Real.log resistance := by field_simp [clockLogPositive.ne']
  rw [logarithmIdentity, Real.exp_neg, Real.exp_log resistancePositive]

end
end IGSIII34.Spectral
