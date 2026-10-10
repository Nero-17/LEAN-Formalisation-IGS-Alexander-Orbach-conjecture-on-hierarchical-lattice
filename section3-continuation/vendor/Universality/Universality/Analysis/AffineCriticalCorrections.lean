import Universality.Analysis.PowerNormalizedResponse
import Universality.Analysis.LocalExponentialComparison

namespace Universality
noncomputable section
set_option maxHeartbeats 800000

theorem affine_additive_power_correction
    (value next coefficient forcing distance nextDistance expansion bound power : ℝ)
    (hnext : 0 ≤ next) (hcoefficient : coefficient ≤ 1)
    (hequation : value = coefficient * next + forcing)
    (hdistance : 0 ≤ distance) (hexpansion : 1 < expansion)
    (hgrowth : expansion * distance ≤ nextDistance)
    (hbound : 0 ≤ bound) (hpower : 0 < power)
    (hforcing : forcing ≤ bound * distance ^ power) :
    value + (bound / (expansion ^ power - 1)) * distance ^ power ≤
      next + (bound / (expansion ^ power - 1)) * nextDistance ^ power := by
  have hpowerExpansion : 1 < expansion ^ power := Real.one_lt_rpow hexpansion hpower
  have hdenominator : 0 < expansion ^ power - 1 := sub_pos.mpr hpowerExpansion
  have hcorrection : 0 ≤ bound / (expansion ^ power - 1) := div_nonneg hbound hdenominator.le
  have hpowers : expansion ^ power * distance ^ power ≤ nextDistance ^ power := by
    rw [← Real.mul_rpow (zero_lt_one.trans hexpansion).le hdistance]
    exact Real.rpow_le_rpow (mul_nonneg (zero_lt_one.trans hexpansion).le hdistance) hgrowth hpower.le
  have hmultiplied := mul_le_mul_of_nonneg_left hpowers hcorrection
  have hidentity : (bound / (expansion ^ power - 1)) * (expansion ^ power - 1) = bound :=
    div_mul_cancel₀ _ hdenominator.ne'
  have hbase := mul_le_mul_of_nonneg_right hcoefficient hnext
  rw [one_mul] at hbase
  have hidentityScaled := congrArg (fun x : ℝ => x * distance ^ power) hidentity
  nlinarith [mul_nonneg hcorrection (Real.rpow_nonneg hdistance power)]

theorem affine_exponential_correction
    (value next coefficient forcing distance nextDistance expansion rate : ℝ)
    (hnext : 0 ≤ next) (hforcing : 0 ≤ forcing)
    (hequation : value = coefficient * next + forcing)
    (hexpansion : 1 < expansion) (hrate : 0 < rate)
    (hgrowth : expansion * distance ≤ nextDistance)
    (hcoefficient : 1 ≤ Real.exp (rate * distance) * coefficient) :
    Real.exp (-(rate / (expansion - 1)) * nextDistance) * next ≤
      Real.exp (-(rate / (expansion - 1)) * distance) * value := by
  have hdenominator : 0 < expansion - 1 := sub_pos.mpr hexpansion
  have hpositive : 0 < rate / (expansion - 1) := div_pos hrate hdenominator
  have hidentity : (rate / (expansion - 1)) * (expansion - 1) = rate :=
    div_mul_cancel₀ _ hdenominator.ne'
  have hidentityScaled := congrArg (fun x : ℝ => x * distance) hidentity
  have hcomparison : -(rate / (expansion - 1)) * nextDistance ≤
      -(rate / (expansion - 1)) * distance - rate * distance := by
    have hh := mul_le_mul_of_nonneg_left hgrowth hpositive.le
    nlinarith
  have hcoeffBound : Real.exp (-(rate / (expansion - 1)) * nextDistance) ≤
      Real.exp (-(rate / (expansion - 1)) * distance) * coefficient := by
    apply (Real.exp_le_exp.mpr hcomparison).trans
    have hh := mul_le_mul_of_nonneg_left hcoefficient
      (Real.exp_pos (-(rate / (expansion - 1)) * distance - rate * distance)).le
    rw [mul_one, ← mul_assoc, ← Real.exp_add] at hh
    have heq : (-(rate / (expansion - 1)) * distance - rate * distance) + rate * distance =
        -(rate / (expansion - 1)) * distance := by ring
    rwa [heq] at hh
  have hproduct := mul_le_mul_of_nonneg_right hcoeffBound hnext
  have hbase : coefficient * next ≤ value := by linarith
  exact hproduct.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le)

end
end Universality
