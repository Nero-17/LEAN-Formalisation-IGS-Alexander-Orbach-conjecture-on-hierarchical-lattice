import IGSIII34.Diffusion.WeightedExponentialNoiseCompletion20261011
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators _root_.Topology

variable {Outcome : Type*} [MeasurableSpace Outcome]

theorem weightedExponentialNoise_product_measurable_completion20261011
    (weights : Outcome → ℕ → ℝ) (weightsMeasurable : ∀ index, Measurable (fun outcome => weights outcome index))
    (count : ℕ) : Measurable (fun sample : Outcome × (ℕ → ℝ) =>
      weightedExponentialNoiseCompletion20261011 (weights sample.1) count sample.2) := by
  unfold weightedExponentialNoiseCompletion20261011
  apply Finset.measurable_sum
  intro index _
  exact ((weightsMeasurable index).comp measurable_fst).mul
    (((measurable_pi_apply index).comp measurable_snd).sub measurable_const)

/-- Conditioning on the entire chain leaves genuine independent exponential
noise. The estimate is uniform over every bounded chain-dependent weight. -/
theorem weightedExponentialNoise_product_probability_bound_completion20261011
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (weights : Outcome → ℕ → ℝ) (weightsMeasurable : ∀ index, Measurable (fun outcome => weights outcome index))
    (count : ℕ) (bound threshold : ℝ) (thresholdPositive : 0 < threshold)
    (bounded : ∀ outcome index, index < count → |weights outcome index| ≤ bound) :
    (law.prod exponentialHoldingTimeLaw) {sample | threshold ≤
      |weightedExponentialNoiseCompletion20261011 (weights sample.1) count sample.2|} ≤
      ENNReal.ofReal ((count : ℝ) * bound ^ 2 / threshold ^ 2) := by
  have eventMeasurable : MeasurableSet {sample : Outcome × (ℕ → ℝ) | threshold ≤
      |weightedExponentialNoiseCompletion20261011 (weights sample.1) count sample.2|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (weightedExponentialNoise_product_measurable_completion20261011 weights weightsMeasurable count))
  rw [Measure.prod_apply eventMeasurable]
  calc
    _ ≤ ∫⁻ _outcome, ENNReal.ofReal ((count : ℝ) * bound ^ 2 / threshold ^ 2) ∂law := by
      apply lintegral_mono
      intro outcome
      exact weightedExponentialNoise_probability_bound_completion20261011 (weights outcome) count bound threshold
        thresholdPositive (bounded outcome)
    _ = _ := by simp

theorem weightedExponentialNoise_product_small_completion20261011
    (laws : ℕ → Measure Outcome) [∀ depth, IsProbabilityMeasure (laws depth)]
    (weights : ℕ → Outcome → ℕ → ℝ)
    (weightsMeasurable : ∀ depth index, Measurable (fun outcome => weights depth outcome index))
    (counts : ℕ → ℕ) (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (bound horizon : ℝ) (boundNonnegative : 0 ≤ bound) (horizonNonnegative : 0 ≤ horizon)
    (bounded : ∀ depth outcome index, index < counts depth → |weights depth outcome index| ≤ bound)
    (countBound : ∀ depth, (counts depth : ℝ) ≤ acceleration depth * horizon + 1)
    (divergence : Tendsto acceleration atTop atTop) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw {sample | acceleration depth * tolerance ≤
      |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (counts depth) sample.2|})
      atTop (𝓝 0) := by
  have inverse : Tendsto (fun depth => (acceleration depth)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp divergence
  have comparison : Tendsto (fun depth => ENNReal.ofReal
      ((horizon / acceleration depth + 1 / acceleration depth ^ 2) * (bound ^ 2 / tolerance ^ 2))) atTop (𝓝 0) := by
    have first := inverse.const_mul horizon
    have second := inverse.pow 2
    have combined := (first.add second).mul_const (bound ^ 2 / tolerance ^ 2)
    have realConvergence : Tendsto (fun depth =>
      (horizon / acceleration depth + 1 / acceleration depth ^ 2) * (bound ^ 2 / tolerance ^ 2)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero, zero_add, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using combined
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConvergence
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds comparison (fun _ => bot_le)
  intro depth
  have estimate := weightedExponentialNoise_product_probability_bound_completion20261011 (laws depth)
    (weights depth) (weightsMeasurable depth) (counts depth) bound (acceleration depth * tolerance)
    (mul_pos (accelerationPositive depth) tolerancePositive) (bounded depth)
  apply estimate.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((acceleration depth * horizon + 1) * bound ^ 2) / (acceleration depth * tolerance) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (countBound depth) (sq_nonneg bound)) (sq_nonneg _)
    _ = _ := by field_simp [(accelerationPositive depth).ne', tolerancePositive.ne'] <;> ring

end
end IGSIII34.Diffusion
