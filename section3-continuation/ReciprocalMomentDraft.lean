import IGSIII34.Probability.LogMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology ENNReal NNReal

theorem integral_mul_reciprocal_integral_ge_one
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Sample → ℝ) (measurable : Measurable value)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (integrable : Integrable value measure) (inverseIntegrable : Integrable (fun sample => (value sample)⁻¹) measure) :
    1 ≤ (∫ sample, value sample ∂measure)*(∫ sample, (value sample)⁻¹ ∂measure) := by
  have nonnegative := positive.mono (fun _ h => h.le)
  have inverseNonnegative := positive.mono (fun _ h => (inv_pos.mpr h).le)
  have firstSquareIntegrable : Integrable (fun sample => (Real.sqrt (value sample))^2) measure :=
    integrable.congr (positive.mono (fun sample h => (Real.sq_sqrt h.le).symm))
  have secondSquareIntegrable : Integrable (fun sample => (Real.sqrt ((value sample)⁻¹))^2) measure :=
    inverseIntegrable.congr (positive.mono (fun sample h => (Real.sq_sqrt (inv_pos.mpr h).le).symm))
  have firstMemLp := (memLp_two_iff_integrable_sq measurable.sqrt.aestronglyMeasurable).mpr firstSquareIntegrable
  have secondMemLp := (memLp_two_iff_integrable_sq measurable.inv.sqrt.aestronglyMeasurable).mpr secondSquareIntegrable
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := measure) (p := 2) (q := 2)
    (f := fun sample => Real.sqrt (value sample)) (g := fun sample => Real.sqrt ((value sample)⁻¹))
    (by exact Real.HolderConjugate.two_two)
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    (by simpa only [ENNReal.ofReal_ofNat] using firstMemLp)
    (by simpa only [ENNReal.ofReal_ofNat, Pi.inv_apply] using secondMemLp)
  have productOne : (∫ sample, Real.sqrt (value sample)*Real.sqrt ((value sample)⁻¹) ∂measure) = 1 := by
    calc
      _ = ∫ _sample : Sample, (1 : ℝ) ∂measure := integral_congr_ae (by
      filter_upwards [positive] with sample valuePositive
      rw [← Real.sqrt_mul valuePositive.le, mul_inv_cancel₀ valuePositive.ne', Real.sqrt_one])
      _ = 1 := by simp
  have firstIdentity : (∫ sample, (Real.sqrt (value sample))^(2 : ℝ) ∂measure) = ∫ sample, value sample ∂measure := by
    apply integral_congr_ae
    filter_upwards [positive] with sample valuePositive
    rw [Real.rpow_two, Real.sq_sqrt valuePositive.le]
  have secondIdentity : (∫ sample, (Real.sqrt ((value sample)⁻¹))^(2 : ℝ) ∂measure) = ∫ sample, (value sample)⁻¹ ∂measure := by
    apply integral_congr_ae
    filter_upwards [positive] with sample valuePositive
    rw [Real.rpow_two, Real.sq_sqrt (inv_pos.mpr valuePositive).le]
  rw [productOne, firstIdentity, secondIdentity] at holder
  have firstNonnegative := integral_nonneg_of_ae nonnegative
  have secondNonnegative := integral_nonneg_of_ae inverseNonnegative
  have firstSq := Real.sq_sqrt firstNonnegative
  have secondSq := Real.sq_sqrt secondNonnegative
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at holder
  have squared := mul_self_le_mul_self (zero_le_one : (0 : ℝ) ≤ 1) holder
  nlinarith [mul_pow (Real.sqrt (∫ sample, value sample ∂measure))
    (Real.sqrt (∫ sample, (value sample)⁻¹ ∂measure)) 2]

theorem moment_log_div_nat_tendsto_zero_of_uniform_real_moments
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    (nonnegative : ∀ depth sample, 0 ≤ value depth sample)
    (positive : ∀ depth, ∀ᵐ sample ∂measure, 0 < value depth sample)
    (moments : ∀ exponent : ℝ, ∃ bound : ℝ, ∀ depth,
      Integrable (fun sample => (value depth sample)^exponent) measure ∧
        (∫ sample, (value depth sample)^exponent ∂measure) ≤ bound)
    (exponent : ℝ) :
    Tendsto (fun depth : ℕ => Real.log (∫ sample, (value depth sample)^exponent ∂measure)/depth) atTop (𝓝 0) := by
  obtain ⟨upper, upperBounds⟩ := moments exponent
  obtain ⟨inverseUpper, inverseBounds⟩ := moments (-exponent)
  have upperPositive : 0 < max 1 upper := zero_lt_one.trans_le (le_max_left _ _)
  have inverseUpperPositive : 0 < max 1 inverseUpper := zero_lt_one.trans_le (le_max_left _ _)
  apply tendsto_div_nat_of_bounded _ (Real.log (max 1 upper)+Real.log (max 1 inverseUpper))
  intro depth
  have inverseIdentity : (fun sample => ((value depth sample)^exponent)⁻¹) =
      (fun sample => (value depth sample)^(-exponent)) := by
    funext sample
    exact (Real.rpow_neg (nonnegative depth sample) exponent).symm
  have productBound := integral_mul_reciprocal_integral_ge_one measure
    (fun sample => (value depth sample)^exponent)
    ((measurable depth).pow measurable_const)
    ((positive depth).mono (fun sample valuePositive => Real.rpow_pos_of_pos valuePositive exponent))
    (upperBounds depth).1 (by rw [inverseIdentity]; exact (inverseBounds depth).1)
  rw [inverseIdentity] at productBound
  have meanNonnegative : 0 ≤ ∫ sample, (value depth sample)^exponent ∂measure :=
    integral_nonneg (fun sample => Real.rpow_nonneg (nonnegative depth sample) exponent)
  have boundedProduct := productBound.trans (mul_le_mul_of_nonneg_left
    ((inverseBounds depth).2.trans (le_max_right 1 inverseUpper)) meanNonnegative)
  have meanPositive : 0 < ∫ sample, (value depth sample)^exponent ∂measure := by
    by_contra notPositive
    have meanZero := le_antisymm (le_of_not_gt notPositive) meanNonnegative
    rw [meanZero, zero_mul] at boundedProduct
    norm_num at boundedProduct
  have lowerBound : 1/(max 1 inverseUpper) ≤ ∫ sample, (value depth sample)^exponent ∂measure :=
    (div_le_iff₀ inverseUpperPositive).mpr boundedProduct
  have lowerLog := Real.log_le_log (one_div_pos.mpr inverseUpperPositive) lowerBound
  have upperLog := Real.log_le_log meanPositive ((upperBounds depth).2.trans (le_max_right 1 upper))
  rw [one_div, Real.log_inv] at lowerLog
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (le_max_left 1 upper), Real.log_nonneg (le_max_left 1 inverseUpper)]

end
end IGSIII34.Probability
