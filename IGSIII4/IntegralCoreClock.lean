import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory

/-- An expectation Cauchy--Schwarz inequality obtained directly from the
pointwise core energy bound; no independence between size and resistance. -/
theorem integral_sq_le_product_of_pointwise_square_bound
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (distance size resistance : Sample → ℝ)
    (distanceIntegrable : Integrable distance measure) (sizeIntegrable : Integrable size measure)
    (resistanceIntegrable : Integrable resistance measure)
    (sizeNonnegative : ∀ᵐ sample ∂measure, 0 ≤ size sample)
    (resistanceNonnegative : ∀ᵐ sample ∂measure, 0 ≤ resistance sample)
    (sizeMeanPositive : 0 < ∫ sample, size sample ∂measure)
    (pointwise : ∀ᵐ sample ∂measure, distance sample ^ 2 ≤ size sample * resistance sample) :
    (∫ sample, distance sample ∂measure) ^ 2 ≤
      (∫ sample, size sample ∂measure) * ∫ sample, resistance sample ∂measure := by
  have trialBound (scalar : ℝ) :
      2 * scalar * (∫ sample, distance sample ∂measure) ≤
        scalar ^ 2 * (∫ sample, size sample ∂measure) + ∫ sample, resistance sample ∂measure := by
    have pointwiseTrial : ∀ᵐ sample ∂measure,
        2 * scalar * distance sample ≤ scalar ^ 2 * size sample + resistance sample := by
      filter_upwards [sizeNonnegative, resistanceNonnegative, pointwise] with sample sizePositive resistancePositive bound
      by_cases sizeStrict : 0 < size sample
      · apply (mul_le_mul_iff_of_pos_right sizeStrict).mp
        nlinarith only [bound, sq_nonneg (scalar * size sample - distance sample)]
      · have sizeZero : size sample = 0 := le_antisymm (le_of_not_gt sizeStrict) sizePositive
        rw [sizeZero] at bound ⊢
        have distanceZero : distance sample = 0 := by nlinarith only [bound, sq_nonneg (distance sample)]
        simpa only [distanceZero, mul_zero, zero_add] using resistancePositive
    have integralBound := integral_mono_ae (distanceIntegrable.const_mul (2 * scalar))
      ((sizeIntegrable.const_mul (scalar ^ 2)).add resistanceIntegrable) pointwiseTrial
    simpa only [Pi.add_apply, integral_const_mul, integral_add (sizeIntegrable.const_mul (scalar ^ 2)) resistanceIntegrable] using integralBound
  have bound := mul_le_mul_of_nonneg_right
    (trialBound ((∫ sample, distance sample ∂measure) / (∫ sample, size sample ∂measure))) sizeMeanPositive.le
  have firstIdentity :
      (2 * ((∫ sample, distance sample ∂measure) / (∫ sample, size sample ∂measure)) *
        (∫ sample, distance sample ∂measure)) * (∫ sample, size sample ∂measure) =
      2 * (∫ sample, distance sample ∂measure) ^ 2 := by
    field_simp [sizeMeanPositive.ne']
  have secondIdentity :
      (((∫ sample, distance sample ∂measure) / (∫ sample, size sample ∂measure)) ^ 2 *
        (∫ sample, size sample ∂measure)) * (∫ sample, size sample ∂measure) =
      (∫ sample, distance sample ∂measure) ^ 2 := by
    field_simp [sizeMeanPositive.ne']
  rw [firstIdentity, add_mul, secondIdentity] at bound
  nlinarith only [bound]

end
end IGSIII4
