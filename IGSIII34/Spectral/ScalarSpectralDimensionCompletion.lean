import IGSIII34.Spectral.LogCorrectedDimension
import IGSIII34.Spectral.ScalarSpeedMeasureCompletion
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Spectral
noncomputable section
open Filter MeasureTheory
open scoped _root_.Topology

/-- Constant speed-measure changes preserve the logarithmic spectral
dimension, including any zero values of the original kernel. -/
theorem scalar_speed_spectral_dimension_completion
    (kernel : ℝ → ℝ) (dimension constant : ℝ) (constantPositive : 0 < constant)
    (original : Tendsto (fun time => -2 * Real.log (kernel time) / Real.log time)
      (𝓝[>] (0:ℝ)) (𝓝 dimension)) :
    Tendsto (fun time => -2 * Real.log (constant⁻¹ * kernel (time / constant)) / Real.log time)
      (𝓝[>] (0:ℝ)) (𝓝 dimension) := by
  have timeChange : Tendsto (fun time : ℝ => time / constant) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    have raw := tendsto_comap (f := fun time : ℝ => constant⁻¹ * time) (x := 𝓝[>] (0:ℝ))
    rw [comap_mulLeft_nhdsGT_zero (inv_pos.mpr constantPositive)] at raw
    simpa only [div_eq_mul_inv, mul_comm] using raw
  have small : Tendsto (fun time : ℝ => Real.log constant / Real.log time) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_log_nhdsGT_zero.const_mul (Real.log constant)
  have negative : ∀ᶠ time : ℝ in 𝓝[>] (0:ℝ), Real.log time < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot 0)
  have scaledNegative : ∀ᶠ time : ℝ in 𝓝[>] (0:ℝ), Real.log (time / constant) < 0 :=
    (Real.tendsto_log_nhdsGT_zero.comp timeChange).eventually (eventually_lt_atBot 0)
  have ratio : Tendsto (fun time : ℝ => Real.log (time / constant) / Real.log time)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have limit := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1)).sub small
    have normalized : Tendsto (fun time : ℝ => 1 - Real.log constant / Real.log time)
        (𝓝[>] (0:ℝ)) (𝓝 1) := by simpa only [sub_zero] using limit
    apply normalized.congr'
    filter_upwards [negative, self_mem_nhdsWithin] with time logarithm timePositive
    rw [Real.log_div (ne_of_gt timePositive) constantPositive.ne']
    field_simp [logarithm.ne]
  have base : Tendsto (fun time => -2 * Real.log (kernel (time / constant)) / Real.log time)
      (𝓝[>] (0:ℝ)) (𝓝 dimension) := by
    have combined := (original.comp timeChange).mul ratio
    have normalized : Tendsto (fun time =>
        (-2 * Real.log (kernel (time / constant)) / Real.log (time / constant)) *
          (Real.log (time / constant) / Real.log time)) (𝓝[>] (0:ℝ)) (𝓝 dimension) := by
      simpa only [mul_one, Function.comp_apply] using combined
    apply normalized.congr'
    filter_upwards [negative, scaledNegative] with time logarithm scaledLogarithm
    field_simp [logarithm.ne, scaledLogarithm.ne]
  have errorBound : ∀ time : ℝ,
      ‖(-2 * Real.log (constant⁻¹ * kernel (time / constant)) / Real.log time) -
        (-2 * Real.log (kernel (time / constant)) / Real.log time)‖ ≤
      ‖-2 * Real.log constant⁻¹ / Real.log time‖ := by
    intro time
    by_cases zero : kernel (time / constant) = 0
    · simp only [zero, mul_zero, Real.log_zero, zero_div, sub_zero, norm_zero]
      exact norm_nonneg _
    · rw [Real.log_mul (inv_ne_zero constantPositive.ne') zero]
      have identity : -2 * (Real.log constant⁻¹ + Real.log (kernel (time / constant))) / Real.log time -
          (-2 * Real.log (kernel (time / constant)) / Real.log time) =
          -2 * Real.log constant⁻¹ / Real.log time := by ring
      rw [identity]
  have errorZero : Tendsto (fun time =>
      (-2 * Real.log (constant⁻¹ * kernel (time / constant)) / Real.log time) -
        (-2 * Real.log (kernel (time / constant)) / Real.log time)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) errorBound
    have limit := (tendsto_inv_log_nhdsGT_zero.const_mul (-2 * Real.log constant⁻¹)).norm
    simpa only [div_eq_mul_inv, mul_zero, norm_zero] using limit
  have combined := errorZero.add base
  simpa only [sub_add_cancel, zero_add] using combined

theorem scalar_speed_spectral_dimension_ae_completion
    {Space : Type*} [MeasurableSpace Space] (measure : Measure Space)
    (kernel : Space → ℝ → ℝ) (dimension : Space → ℝ)
    (constant : ℝ) (constantPositive : 0 < constant)
    (original : ∀ᵐ point ∂measure, Tendsto (fun time => -2 * Real.log (kernel point time) / Real.log time)
      (𝓝[>] (0:ℝ)) (𝓝 (dimension point))) :
    ∀ᵐ point ∂scalarSpeedMeasureCompletion measure constant,
      Tendsto (fun time => -2 * Real.log (constant⁻¹ * kernel point (time / constant)) / Real.log time)
        (𝓝[>] (0:ℝ)) (𝓝 (dimension point)) := by
  apply Measure.ae_smul_measure _ (ENNReal.ofReal constant)
  filter_upwards [original] with point limit
  exact scalar_speed_spectral_dimension_completion (kernel point) (dimension point) constant constantPositive limit

end
end IGSIII34.Spectral
