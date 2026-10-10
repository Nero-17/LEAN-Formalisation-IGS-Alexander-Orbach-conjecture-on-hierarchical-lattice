import IGSIII34.Probability.InverseMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped ENNReal
variable {Sample : Type*} [MeasurableSpace Sample]

theorem integrable_real_power_of_all_natural_moments
    (measure : Measure Sample) [IsFiniteMeasure measure] (value : Sample → ℝ)
    (measurable : Measurable value) (positive : ∀ᵐ sample ∂measure, 0 < value sample)
    (positiveMoments : ∀ power : ℕ, (∫⁻ sample, ENNReal.ofReal (value sample)^power ∂measure) ≠ ∞)
    (inverseMoments : ∀ power : ℕ, (∫⁻ sample, (ENNReal.ofReal (value sample))⁻¹^power ∂measure) ≠ ∞)
    (exponent : ℝ) : Integrable (fun sample => value sample^exponent) measure := by
  have absoluteNatural (power : ℕ) : Integrable (fun sample => |value sample|^power) measure := by
    have result := integrable_toReal_of_lintegral_ne_top
      ((ENNReal.continuous_ofReal.measurable.comp measurable).pow_const power).aemeasurable (positiveMoments power)
    apply result.congr
    filter_upwards [positive] with sample valuePositive
    simp only [Function.comp_apply, ENNReal.toReal_pow, ENNReal.toReal_ofReal valuePositive.le, abs_of_pos valuePositive]
  have inverseAbsoluteNatural (power : ℕ) : Integrable (fun sample => (|value sample|)⁻¹^power) measure := by
    have result := integrable_toReal_of_lintegral_ne_top
      ((ENNReal.continuous_ofReal.measurable.comp measurable).inv.pow_const power).aemeasurable (inverseMoments power)
    apply result.congr
    filter_upwards [positive] with sample valuePositive
    simp only [Function.comp_apply, Pi.inv_apply, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal valuePositive.le, abs_of_pos valuePositive]
  have absoluteMeasurable : Measurable (fun sample => |value sample|) := continuous_abs.measurable.comp measurable
  by_cases exponentNonnegative : 0 ≤ exponent
  · have result := integrable_rpow_of_nat_moments measure absoluteMeasurable
      (fun sample => abs_nonneg (value sample)) absoluteNatural exponentNonnegative
    apply result.congr
    filter_upwards [positive] with sample valuePositive
    rw [abs_of_pos valuePositive]
  · have result := integrable_rpow_of_nat_moments measure absoluteMeasurable.inv
      (fun sample => inv_nonneg.mpr (abs_nonneg (value sample))) inverseAbsoluteNatural
      (neg_nonneg.mpr (le_of_not_ge exponentNonnegative))
    apply result.congr
    filter_upwards [positive] with sample valuePositive
    simp only [Pi.inv_apply]
    rw [abs_of_pos valuePositive, ← Real.rpow_neg_eq_inv_rpow, neg_neg]

end
end IGSIII34.Probability
