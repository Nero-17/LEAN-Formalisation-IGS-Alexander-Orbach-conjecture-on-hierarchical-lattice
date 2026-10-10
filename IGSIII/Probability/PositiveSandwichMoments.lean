import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory
open scoped ENNReal

theorem lintegral_positive_power_le_of_sandwich
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value base : Sample → ℝ) (upper : ℝ) (upperNonnegative : 0 ≤ upper)
    (bound : ∀ᵐ sample ∂measure, value sample ≤ upper * base sample) (power : ℕ) :
    (∫⁻ sample, ENNReal.ofReal (value sample) ^ power ∂measure) ≤
      ENNReal.ofReal upper ^ power * (∫⁻ sample, ENNReal.ofReal (base sample) ^ power ∂measure) := by
  calc
    _ ≤ ∫⁻ sample, ENNReal.ofReal (upper * base sample) ^ power ∂measure :=
      lintegral_mono_ae (bound.mono (fun _ inequality => pow_le_pow_left' (ENNReal.ofReal_le_ofReal inequality) power))
    _ = _ := by
      simp only [ENNReal.ofReal_mul upperNonnegative, mul_pow]
      exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem lintegral_inverse_power_le_of_sandwich
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value base : Sample → ℝ) (lower : ℝ) (lowerPositive : 0 < lower)
    (bound : ∀ᵐ sample ∂measure, lower * base sample ≤ value sample) (power : ℕ) :
    (∫⁻ sample, (ENNReal.ofReal (value sample))⁻¹ ^ power ∂measure) ≤
      (ENNReal.ofReal lower)⁻¹ ^ power * (∫⁻ sample, (ENNReal.ofReal (base sample))⁻¹ ^ power ∂measure) := by
  calc
    _ ≤ ∫⁻ sample, (ENNReal.ofReal (lower * base sample))⁻¹ ^ power ∂measure :=
      lintegral_mono_ae (bound.mono (fun _ inequality =>
        pow_le_pow_left' (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal inequality)) power))
    _ = _ := by
      simp only [ENNReal.ofReal_mul lowerPositive.le,
        ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr lowerPositive).ne')
          (Or.inl ENNReal.ofReal_ne_top), mul_pow]
      exact lintegral_const_mul' _ _
        (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr lowerPositive).ne'))

theorem lintegral_exponential_le_of_sandwich
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value base : Sample → ℝ) (upper parameter : ℝ) (parameterNonnegative : 0 ≤ parameter)
    (bound : ∀ᵐ sample ∂measure, value sample ≤ upper * base sample) :
    (∫⁻ sample, ENNReal.ofReal (Real.exp (parameter * value sample)) ∂measure) ≤
      ∫⁻ sample, ENNReal.ofReal (Real.exp ((parameter * upper) * base sample)) ∂measure := by
  apply lintegral_mono_ae
  filter_upwards [bound] with sample inequality
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left inequality parameterNonnegative

theorem memLp_of_all_positive_natural_moments
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsFiniteMeasure measure] (value : Sample → ℝ) (measurable : Measurable value)
    (nonnegative : ∀ᵐ sample ∂measure, 0 ≤ value sample)
    (finiteMoments : ∀ power : ℕ, (∫⁻ sample, ENNReal.ofReal (value sample) ^ power ∂measure) ≠ ∞)
    (order : ℝ≥0∞) (orderPositive : order ≠ 0) (orderFinite : order ≠ ∞) :
    MemLp value order measure := by
  obtain ⟨power, powerLarge⟩ := exists_nat_gt order.toReal
  have integralPower : Integrable (fun sample => ‖value sample‖ ^ (power : ℝ)) measure := by
    simp only [Real.rpow_natCast]
    have identity : (fun sample => ENNReal.ofReal (‖value sample‖ ^ power)) =ᵐ[measure]
        fun sample => ENNReal.ofReal (value sample) ^ power := by
      filter_upwards [nonnegative] with sample sampleNonnegative
      rw [Real.norm_eq_abs, abs_of_nonneg sampleNonnegative, ENNReal.ofReal_pow sampleNonnegative]
    refine ⟨measurable.norm.pow_const power |>.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun sample => pow_nonneg (norm_nonneg _) power))).mpr
    rw [lintegral_congr_ae identity]
    exact (finiteMoments power).lt_top
  apply (integrable_norm_rpow_iff measurable.aestronglyMeasurable orderPositive orderFinite).mp
  exact integrable_norm_rpow_of_le measurable.aestronglyMeasurable ENNReal.toReal_nonneg
    (Nat.cast_nonneg power) powerLarge.le integralPower

end IGSIII.Probability
