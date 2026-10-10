import IGSIII34.Probability.UniformSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem real_moment_tendsto_of_ae_and_uniform_real_moments
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
    (exponent : ℝ) :
    Tendsto (fun depth => ∫ sample, (sequence depth sample)^exponent ∂measure) atTop
      (𝓝 (∫ sample, (endpoint sample)^exponent ∂measure)) := by
  obtain ⟨bound, bounds⟩ := uniformMoments (2*exponent)
  have squareEquality (depth : ℕ) : (fun sample => ((sequence depth sample)^exponent)^2) =ᵐ[measure]
      (fun sample => (sequence depth sample)^(2*exponent)) := by
    filter_upwards [positive depth] with sample inequality
    have equality := Real.rpow_mul inequality.le exponent 2
    rw [Real.rpow_two] at equality
    simpa only [mul_comm exponent (2 : ℝ)] using equality.symm
  have ui := unifIntegrable_one_of_uniform_second_moment measure
    (fun depth sample => (sequence depth sample)^exponent)
    (fun depth => (measurable depth).pow measurable_const)
    (fun depth => (bounds depth).1.congr (squareEquality depth).symm)
    (fun depth => ((uniformMoments exponent).choose_spec depth).1)
    bound (fun depth => by rw [integral_congr_ae (squareEquality depth)]; exact (bounds depth).2)
  have powerConvergence : ∀ᵐ sample ∂measure,
      Tendsto (fun depth => (sequence depth sample)^exponent) atTop (𝓝 ((endpoint sample)^exponent)) := by
    filter_upwards [convergence, endpointPositive] with sample limit inequality
    exact (Real.continuousAt_rpow_const (endpoint sample) exponent (Or.inl inequality.ne')).tendsto.comp limit
  have lpConvergence := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (fun depth => ((measurable depth).pow measurable_const).aestronglyMeasurable)
    (memLp_one_iff_integrable.mpr (endpointMoments exponent)) ui powerConvergence
  exact tendsto_integral_of_L1' _ (endpointMeasurable.pow measurable_const).aestronglyMeasurable
    (Eventually.of_forall (fun depth => ((uniformMoments exponent).choose_spec depth).1)) lpConvergence

end
end IGSIII34.Probability

