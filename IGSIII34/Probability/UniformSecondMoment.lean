import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

theorem unifIntegrable_one_of_uniform_second_moment
    {Sample Index : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : Index → Sample → ℝ) (measurable : ∀ index, Measurable (sequence index))
    (squareIntegrable : ∀ index, Integrable (fun sample => (sequence index sample)^2) measure)
    (integrable : ∀ index, Integrable (sequence index) measure)
    (bound : ℝ) (bounds : ∀ index, (∫ sample, (sequence index sample)^2 ∂measure) ≤ bound) :
    UnifIntegrable sequence 1 measure := by
  apply unifIntegrable_of (by norm_num) (by norm_num) (fun index => (measurable index).aestronglyMeasurable)
  intro tolerance tolerancePositive
  let cutoff : ℝ := max 1 bound/tolerance
  have cutoffPositive : 0 < cutoff := div_pos (zero_lt_one.trans_le (le_max_left _ _)) tolerancePositive
  refine ⟨⟨cutoff, cutoffPositive.le⟩, fun index => ?_⟩
  let tail : Set Sample := {sample | (⟨cutoff, cutoffPositive.le⟩ : ℝ≥0) ≤ ‖sequence index sample‖₊}
  have tailMeasurable : MeasurableSet tail := (measurable index).nnnorm measurableSet_Ici
  have tailIntegrable := (integrable index).indicator tailMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm tailIntegrable]
  apply ENNReal.ofReal_le_ofReal
  have inequality : (∫ sample, ‖tail.indicator (sequence index) sample‖ ∂measure) ≤
      (∫ sample, (sequence index sample)^2 ∂measure)/cutoff := by
    rw [← integral_div]
    apply integral_mono_ae tailIntegrable.norm ((squareIntegrable index).div_const cutoff)
    filter_upwards [] with sample
    by_cases within : sample ∈ tail
    · rw [Set.indicator_of_mem within, Real.norm_eq_abs]
      have cutoffBound : cutoff ≤ |sequence index sample| := by
        change (⟨cutoff, cutoffPositive.le⟩ : ℝ≥0) ≤ ‖sequence index sample‖₊ at within
        have normBound : cutoff ≤ ‖sequence index sample‖ := by exact_mod_cast within
        simpa only [Real.norm_eq_abs] using normBound
      apply (le_div_iff₀ cutoffPositive).mpr
      nlinarith [sq_abs (sequence index sample), abs_nonneg (sequence index sample)]
    · rw [Set.indicator_of_notMem within, norm_zero]
      exact div_nonneg (sq_nonneg _) cutoffPositive.le
  calc
    _ ≤ (∫ sample, (sequence index sample)^2 ∂measure)/cutoff := inequality
    _ ≤ max 1 bound/cutoff := div_le_div_of_nonneg_right ((bounds index).trans (le_max_right _ _)) cutoffPositive.le
    _ = tolerance := by
      dsimp only [cutoff]
      field_simp [ne_of_gt (zero_lt_one.trans_le (le_max_left (1 : ℝ) bound))]

end
end IGSIII34.Probability
