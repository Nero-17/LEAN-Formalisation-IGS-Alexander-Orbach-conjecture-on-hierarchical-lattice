import IGSIII34.Spectral.PowerPrefix
import IGSIII34.Spectral.LogCorrectedDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative algebra for the monotone Laplace Tauberian proof.
The Laplace bounds are actual integrals, not abstract fields containing the
desired heat estimate. Construction of the underlying heat kernel is separate.
-/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem scaled_parameter_power (factor time exponent : ℝ)
    (factorPositive : 0 < factor) (timePositive : 0 < time) :
    (factor / time) ^ exponent = factor ^ exponent * time ^ (-exponent) := by
  rw [Real.div_rpow factorPositive.le timePositive.le, Real.rpow_neg timePositive.le]
  exact div_eq_mul_inv _ _

theorem scaled_parameter_times_power (factor time exponent : ℝ)
    (timePositive : 0 < time) :
    factor / time * time ^ (1 - exponent) = factor * time ^ (-exponent) := by
  rw [Real.rpow_sub timePositive, Real.rpow_one, Real.rpow_neg timePositive.le]
  field_simp [timePositive.ne', (Real.rpow_pos_of_pos timePositive exponent).ne']

theorem inverse_parameter_power (time exponent : ℝ) (timePositive : 0 < time) :
    (time⁻¹) ^ (exponent - 1) / time = time ^ (-exponent) := by
  rw [Real.rpow_sub_one (inv_ne_zero timePositive.ne')]
  calc
    _ = (time⁻¹) ^ exponent := by field_simp
    _ = _ := by rw [Real.inv_rpow timePositive.le, Real.rpow_neg timePositive.le]

theorem upper_heat_from_resolvent_power
    (kernel : ℝ → ℝ) (coefficient exponent time : ℝ) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-(time⁻¹) * other) * kernel other) (Ioi 0))
    (upper : diagonalLaplace kernel time⁻¹ ≤ coefficient * (time⁻¹) ^ (exponent - 1)) :
    kernel time ≤ (Real.exp 1 * coefficient) * time ^ (-exponent) := by
  have bound := diagonal_le_exp_mul_laplace_div kernel time timePositive nonnegative decreasing integrable
  have comparison := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left upper (Real.exp_pos 1).le) timePositive.le
  calc
    _ ≤ _ := bound.trans comparison
    _ = (Real.exp 1 * coefficient) * ((time⁻¹) ^ (exponent - 1) / time) := by ring
    _ = _ := by rw [inverse_parameter_power time exponent timePositive]

theorem lower_heat_from_power_split
    (kernel : ℝ → ℝ) (coefficient exponent lowerCoefficient factor time : ℝ)
    (measurable : Measurable kernel) (coefficientNonnegative : 0 ≤ coefficient)
    (exponentBound : exponent < 1) (factorPositive : 0 < factor) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-(factor / time) * other) * kernel other) (Ioi 0))
    (upper : ∀ other ∈ Ioc 0 time, kernel other ≤ coefficient * other ^ (-exponent))
    (resolventLower : lowerCoefficient * (factor / time) ^ (exponent - 1) ≤
      diagonalLaplace kernel (factor / time))
    (factorSmall : 2 * (coefficient / (1 - exponent)) * factor ≤
      lowerCoefficient * factor ^ exponent) :
    lowerCoefficient * factor ^ exponent / 2 * time ^ (-exponent) ≤ kernel time := by
  have parameterPositive := div_pos factorPositive timePositive
  have splitBound := diagonalLaplace_split_power_le kernel coefficient exponent (factor / time) time
    measurable coefficientNonnegative exponentBound parameterPositive timePositive nonnegative decreasing integrable upper
  have productBound := mul_le_mul_of_nonneg_left (resolventLower.trans splitBound) parameterPositive.le
  have leftIdentity : (factor / time) *
      (lowerCoefficient * (factor / time) ^ (exponent - 1)) =
        lowerCoefficient * factor ^ exponent * time ^ (-exponent) := by
    rw [Real.rpow_sub_one parameterPositive.ne']
    calc
      _ = lowerCoefficient * (factor / time) ^ exponent := by field_simp
      _ = _ := by rw [scaled_parameter_power factor time exponent factorPositive timePositive]; ring
  have rightIdentity : (factor / time) *
      (coefficient * time ^ (1 - exponent) / (1 - exponent) + kernel time / (factor / time)) =
        (coefficient / (1 - exponent)) * factor * time ^ (-exponent) + kernel time := by
    rw [mul_add, mul_div_cancel₀ _ parameterPositive.ne']
    have identity := scaled_parameter_times_power factor time exponent timePositive
    calc
      _ = (coefficient / (1 - exponent)) *
          ((factor / time) * time ^ (1 - exponent)) + kernel time := by ring
      _ = _ := by rw [identity]; ring
  rw [leftIdentity, rightIdentity] at productBound
  have coefficientBound := mul_le_mul_of_nonneg_right factorSmall
    (Real.rpow_pos_of_pos timePositive (-exponent)).le
  nlinarith

theorem exists_small_tauberian_factor (lowerCoefficient prefixCoefficient exponent : ℝ)
    (lowerPositive : 0 < lowerCoefficient) (exponentBound : exponent < 1) :
    ∃ factor : ℝ, 0 < factor ∧
      2 * prefixCoefficient * factor ≤ lowerCoefficient * factor ^ exponent := by
  have divergent := tendsto_rpow_neg_nhdsGT_zero (by linarith : exponent - 1 < 0)
  have eventual := divergent.eventually (eventually_gt_atTop (2 * prefixCoefficient / lowerCoefficient))
  have simultaneous : ∀ᶠ factor : ℝ in 𝓝[>] 0,
      0 < factor ∧ 2 * prefixCoefficient / lowerCoefficient < factor ^ (exponent - 1) := by
    filter_upwards [self_mem_nhdsWithin, eventual] with factor positive powerBound
    exact ⟨positive, powerBound⟩
  obtain ⟨factor, positive, powerBound⟩ := simultaneous.exists
  refine ⟨factor, positive, ?_⟩
  have multiplied := mul_le_mul_of_nonneg_right
    ((div_le_iff₀ lowerPositive).mp powerBound.le) positive.le
  rw [Real.rpow_sub_one positive.ne'] at multiplied
  calc
    _ ≤ _ := multiplied
    _ = _ := by field_simp

theorem heat_power_bounds_of_laplace_power_bounds
    (kernel : ℝ → ℝ) (exponent lowerCoefficient upperCoefficient threshold : ℝ)
    (measurable : Measurable kernel) (exponentBound : exponent < 1)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (thresholdPositive : 0 < threshold)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : ∀ parameter, 0 < parameter →
      IntegrableOn (fun time => Real.exp (-parameter * time) * kernel time) (Ioi 0))
    (lower : ∀ parameter, threshold ≤ parameter →
      lowerCoefficient * parameter ^ (exponent - 1) ≤ diagonalLaplace kernel parameter)
    (upper : ∀ parameter, threshold ≤ parameter →
      diagonalLaplace kernel parameter ≤ upperCoefficient * parameter ^ (exponent - 1)) :
    ∃ lowerConstant upperConstant timeBound : ℝ,
      0 < lowerConstant ∧ 0 < upperConstant ∧ 0 < timeBound ∧
      (∀ time ∈ Ioo 0 timeBound, lowerConstant * time ^ (-exponent) ≤ kernel time) ∧
      (∀ time ∈ Ioo 0 timeBound, kernel time ≤ upperConstant * time ^ (-exponent)) := by
  obtain ⟨factor, factorPositive, factorSmall⟩ := exists_small_tauberian_factor
    lowerCoefficient (Real.exp 1 * upperCoefficient / (1 - exponent)) exponent lowerPositive exponentBound
  let timeBound := min (1 / threshold) (factor / threshold)
  have timeBoundPositive : 0 < timeBound :=
    lt_min (div_pos zero_lt_one thresholdPositive) (div_pos factorPositive thresholdPositive)
  have inverseThreshold (time : ℝ) (positive : 0 < time) (small : time < timeBound) :
      threshold ≤ time⁻¹ := by
    have product := (lt_div_iff₀ thresholdPositive).mp (small.trans_le (min_le_left _ _))
    rw [← one_div]
    apply (le_div_iff₀ positive).mpr
    nlinarith
  have heatUpper (time : ℝ) (positive : 0 < time) (small : time < timeBound) :
      kernel time ≤ (Real.exp 1 * upperCoefficient) * time ^ (-exponent) :=
    upper_heat_from_resolvent_power kernel upperCoefficient exponent time positive nonnegative decreasing
      (integrable time⁻¹ (inv_pos.mpr positive)) (upper time⁻¹ (inverseThreshold time positive small))
  refine ⟨lowerCoefficient * factor ^ exponent / 2, Real.exp 1 * upperCoefficient,
    timeBound, by positivity, by positivity, timeBoundPositive, ?_, ?_⟩
  · intro time member
    have parameterPositive := div_pos factorPositive member.1
    have thresholdBound : threshold ≤ factor / time := by
      apply (le_div_iff₀ member.1).mpr
      have product := (lt_div_iff₀ thresholdPositive).mp
        (member.2.trans_le (min_le_right _ _))
      nlinarith
    exact lower_heat_from_power_split kernel (Real.exp 1 * upperCoefficient) exponent
      lowerCoefficient factor time measurable (by positivity) exponentBound factorPositive member.1
      nonnegative decreasing (integrable (factor / time) parameterPositive)
      (fun other otherMember => heatUpper other otherMember.1 (otherMember.2.trans_lt member.2))
      (lower (factor / time) thresholdBound) factorSmall
  · intro time member
    exact heatUpper time member.1 member.2

theorem spectral_dimension_of_laplace_power_bounds
    (kernel : ℝ → ℝ) (exponent lowerCoefficient upperCoefficient threshold : ℝ)
    (measurable : Measurable kernel) (exponentBound : exponent < 1)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (thresholdPositive : 0 < threshold)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : ∀ parameter, 0 < parameter →
      IntegrableOn (fun time => Real.exp (-parameter * time) * kernel time) (Ioi 0))
    (lower : ∀ parameter, threshold ≤ parameter →
      lowerCoefficient * parameter ^ (exponent - 1) ≤ diagonalLaplace kernel parameter)
    (upper : ∀ parameter, threshold ≤ parameter →
      diagonalLaplace kernel parameter ≤ upperCoefficient * parameter ^ (exponent - 1)) :
    Tendsto (fun time => -2 * Real.log (kernel time) / Real.log time)
      (𝓝[>] 0) (𝓝 (2 * exponent)) := by
  obtain ⟨lowerConstant, upperConstant, timeBound, lowerPositive, upperPositive, timePositive,
    lowerBound, upperBound⟩ := heat_power_bounds_of_laplace_power_bounds kernel exponent
      lowerCoefficient upperCoefficient threshold measurable exponentBound lowerPositive upperPositive
      thresholdPositive nonnegative decreasing integrable lower upper
  exact tendsto_spectral_dimension_of_pure_bounds kernel exponent lowerConstant upperConstant timeBound
    lowerPositive upperPositive timePositive lowerBound upperBound

end
end IGSIII34.Spectral
