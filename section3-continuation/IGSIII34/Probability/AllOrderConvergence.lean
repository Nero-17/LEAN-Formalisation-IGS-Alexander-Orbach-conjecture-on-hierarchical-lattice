import IGSIII34.Probability.UniformSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem abs_sub_rpow_le_sum_of_nonnegative (first second exponent : ℝ)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (exponentNonnegative : 0 ≤ exponent) :
    |first-second|^exponent ≤ first^exponent+second^exponent := by
  rcases le_total first second with comparison | comparison
  · have absoluteBound : |first-second| ≤ second := by rw [abs_of_nonpos (sub_nonpos.mpr comparison)]; linarith
    exact (Real.rpow_le_rpow (abs_nonneg _) absoluteBound exponentNonnegative).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg firstNonnegative _))
  · have absoluteBound : |first-second| ≤ first := by rw [abs_of_nonneg (sub_nonneg.mpr comparison)]; linarith
    exact (Real.rpow_le_rpow (abs_nonneg _) absoluteBound exponentNonnegative).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg secondNonnegative _))

theorem absolute_error_moment_tendsto_of_ae_and_uniform_real_moments
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (sequence depth))
    (positive : ∀ depth, ∀ᵐ sample ∂measure, 0 < sequence depth sample)
    (uniformMoments : ∀ exponent : ℝ, ∃ bound : ℝ, ∀ depth,
      Integrable (fun sample => (sequence depth sample)^exponent) measure ∧
        (∫ sample, (sequence depth sample)^exponent ∂measure) ≤ bound)
    (endpoint : Sample → ℝ) (endpointMeasurable : Measurable endpoint)
    (endpointPositive : ∀ᵐ sample ∂measure, 0 < endpoint sample)
    (endpointMoments : ∀ exponent : ℝ, Integrable (fun sample => (endpoint sample)^exponent) measure)
    (convergence : ∀ᵐ sample ∂measure, Tendsto (fun depth => sequence depth sample) atTop (𝓝 (endpoint sample)))
    (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Tendsto (fun depth => ∫ sample, |sequence depth sample-endpoint sample|^exponent ∂measure) atTop (𝓝 0) := by
  let error (depth : ℕ) (sample : Sample) := |sequence depth sample-endpoint sample|^exponent
  have errorMeasurable (depth : ℕ) : Measurable (error depth) :=
    (continuous_abs.measurable.comp ((measurable depth).sub endpointMeasurable)).pow measurable_const
  have errorNonnegative (depth : ℕ) : ∀ sample, 0 ≤ error depth sample :=
    fun sample => Real.rpow_nonneg (abs_nonneg _) _
  have integrablePower (power : ℝ) (powerNonnegative : 0 ≤ power) (depth : ℕ) :
      Integrable (fun sample => |sequence depth sample-endpoint sample|^power) measure := by
    apply (((uniformMoments power).choose_spec depth).1.add (endpointMoments power)).mono'
      ((continuous_abs.measurable.comp ((measurable depth).sub endpointMeasurable)).pow measurable_const).aestronglyMeasurable
    filter_upwards [positive depth, endpointPositive] with sample sequencePositive limitPositive
    change ‖|sequence depth sample-endpoint sample|^power‖ ≤ (sequence depth sample)^power+(endpoint sample)^power
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact abs_sub_rpow_le_sum_of_nonnegative _ _ _ sequencePositive.le limitPositive.le powerNonnegative
  have errorIntegrable (depth : ℕ) : Integrable (error depth) measure := integrablePower exponent exponentPositive.le depth
  have squareEquality (depth : ℕ) : (fun sample => (error depth sample)^2) =
      (fun sample => |sequence depth sample-endpoint sample|^(2*exponent)) := by
    funext sample
    have equality := Real.rpow_mul (abs_nonneg (sequence depth sample-endpoint sample)) exponent 2
    rw [Real.rpow_two] at equality
    simpa only [error, mul_comm exponent (2 : ℝ)] using equality.symm
  obtain ⟨bound, bounds⟩ := uniformMoments (2*exponent)
  have squareBound (depth : ℕ) : (∫ sample, (error depth sample)^2 ∂measure) ≤
      bound+(∫ sample, (endpoint sample)^(2*exponent) ∂measure) := by
    rw [squareEquality]
    calc
      _ ≤ ∫ sample, (sequence depth sample)^(2*exponent)+(endpoint sample)^(2*exponent) ∂measure := by
        apply integral_mono_ae (integrablePower (2*exponent) (by positivity) depth)
          ((bounds depth).1.add (endpointMoments (2*exponent)))
        filter_upwards [positive depth, endpointPositive] with sample sequencePositive limitPositive
        exact abs_sub_rpow_le_sum_of_nonnegative _ _ _ sequencePositive.le limitPositive.le (by positivity)
      _ = _ := by rw [integral_add (bounds depth).1 (endpointMoments (2*exponent))]
      _ ≤ _ := add_le_add (bounds depth).2 le_rfl
  have ui := unifIntegrable_one_of_uniform_second_moment measure error errorMeasurable
    (fun depth => by rw [squareEquality]; exact integrablePower (2*exponent) (by positivity) depth)
    errorIntegrable _ squareBound
  have errorConvergence : ∀ᵐ sample ∂measure, Tendsto (fun depth => error depth sample) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [convergence] with sample limit
    have difference := (limit.sub_const (endpoint sample)).abs
    simp only [sub_self, abs_zero] at difference
    have powered := (Real.continuousAt_rpow_const 0 exponent (Or.inr exponentPositive.le)).tendsto.comp difference
    change Tendsto (fun depth => |sequence depth sample-endpoint sample|^exponent) atTop (𝓝 ((0 : ℝ)^exponent)) at powered
    simpa only [Real.zero_rpow exponentPositive.ne', error] using powered
  have lpConvergence := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (fun depth => (errorMeasurable depth).aestronglyMeasurable)
    (memLp_const (0 : ℝ)) ui errorConvergence
  have integralLimit := tendsto_integral_of_L1' _ (measurable_const : Measurable (fun _ : Sample => (0 : ℝ))).aestronglyMeasurable
    (Eventually.of_forall errorIntegrable) lpConvergence
  simpa only [integral_zero, error] using integralLimit

end
end IGSIII34.Probability



