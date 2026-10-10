import IGSIII.Probability.ExceptionalEnvelope
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Filter
open scoped ENNReal

/-- A countable family with summable power integrals has a single dominating
random variable in the corresponding Lp space. No independence is assumed. -/
theorem exists_memLp_countable_envelope
    {Sample Index : Type*} [MeasurableSpace Sample] [Countable Index]
    (measure : Measure Sample) (power : ℕ) (powerPositive : 0 < power)
    (functions : Index → Sample → ℝ) (measurable : ∀ index, Measurable (functions index))
    (summableIntegrals : (∑' index, ∫⁻ sample, ‖functions index sample‖ₑ ^ power ∂measure) ≠ ∞) :
    ∃ envelope : Sample → ℝ, Measurable envelope ∧ MemLp envelope power measure ∧
      (∀ sample, 0 ≤ envelope sample) ∧
      ∀ᵐ sample ∂measure, ∀ index, ‖functions index sample‖ ≤ envelope sample := by
  let total : Sample → ℝ≥0∞ := fun sample => ∑' index, ‖functions index sample‖ₑ ^ power
  have totalMeasurable : Measurable total :=
    Measurable.ennreal_tsum (fun index => (measurable index).enorm.pow_const power)
  have integralFinite : (∫⁻ sample, total sample ∂measure) ≠ ∞ := by
    rw [show (∫⁻ sample, total sample ∂measure) =
      ∑' index, ∫⁻ sample, ‖functions index sample‖ₑ ^ power ∂measure from
        lintegral_tsum (fun index => ((measurable index).enorm.pow_const power).aemeasurable)]
    exact summableIntegrals
  let envelope : Sample → ℝ := fun sample => (total sample ^ (1 / (power : ℝ))).toReal
  have envelopeMeasurable : Measurable envelope :=
    (totalMeasurable.pow_const (1 / (power : ℝ))).ennreal_toReal
  have powerRealPositive : 0 < (power : ℝ) := by exact_mod_cast powerPositive
  have exponentNonnegative : 0 ≤ 1 / (power : ℝ) := by positivity
  have envelopeNorm : ∀ᵐ sample ∂measure,
      ‖envelope sample‖ₑ = total sample ^ (1 / (power : ℝ)) := by
    filter_upwards [ae_lt_top totalMeasurable integralFinite] with sample finite
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
      (ENNReal.rpow_ne_top_of_nonneg exponentNonnegative finite.ne)]
  have normPower : ∀ᵐ sample ∂measure, ‖envelope sample‖ₑ ^ (power : ℝ) = total sample := by
    filter_upwards [envelopeNorm] with sample identity
    rw [identity, ← ENNReal.rpow_mul, one_div_mul_cancel powerRealPositive.ne', ENNReal.rpow_one]
  refine ⟨envelope, envelopeMeasurable, ?_, fun _ => ENNReal.toReal_nonneg, ?_⟩
  · refine ⟨envelopeMeasurable.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by exact_mod_cast powerPositive.ne') (by simp), ENNReal.toReal_natCast]
    rw [lintegral_congr_ae normPower]
    exact ENNReal.rpow_lt_top_of_nonneg exponentNonnegative integralFinite
  · filter_upwards [envelopeNorm] with sample identity
    intro index
    have comparison : ‖functions index sample‖ₑ ≤ ‖envelope sample‖ₑ := by
      apply (ENNReal.rpow_le_rpow_iff powerRealPositive).mp
      rw [ENNReal.rpow_natCast, identity, ← ENNReal.rpow_mul,
        one_div_mul_cancel powerRealPositive.ne', ENNReal.rpow_one]
      exact ENNReal.le_tsum index
    have realComparison := ENNReal.toReal_mono (show ‖envelope sample‖ₑ ≠ ∞ from enorm_ne_top) comparison
    simpa only [toReal_enorm, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ envelope sample from ENNReal.toReal_nonneg)] using realComparison

end IGSIII.Probability



