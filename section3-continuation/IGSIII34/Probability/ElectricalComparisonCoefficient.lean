import IGSIII34.Probability.ElectricalComparisonWeight
import IGSIII34.Probability.ElectricalDenominator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

theorem electrical_comparison_numerators_tendsto_zero
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (inverseFourth : ∀ depth, Integrable (fun sample => (sequence depth sample)⁻¹^4) measure)
    (limitInverseFourth : Integrable (fun sample => (limit sample)⁻¹^4) measure)
    (bound : ℝ) (inverseBound : ∀ depth, (∫ sample, (sequence depth sample)⁻¹^4 ∂measure) ≤ bound) :
    Tendsto (fun depth => ∫ sample, max (sequence depth sample-limit sample) 0 * max 1 ((limit sample)⁻¹^2) ∂measure)
      atTop (𝓝 0) ∧
    Tendsto (fun depth => ∫ sample, max (limit sample-sequence depth sample) 0 * max 1 ((sequence depth sample)⁻¹^2) ∂measure)
      atTop (𝓝 0) := by
  let referenceWeight := (electricalComparisonWeight_memLp_two measure limit (Lp.stronglyMeasurable limit).measurable limitInverseFourth).toLp
    (fun sample => electricalComparisonWeight (limit sample))
  have referenceEquality := MemLp.coeFn_toLp
    (electricalComparisonWeight_memLp_two measure limit (Lp.stronglyMeasurable limit).measurable limitInverseFourth)
  have referenceNonnegative : 0 ≤ referenceWeight := by
    apply (Lp.coeFn_nonneg referenceWeight).mp
    filter_upwards [referenceEquality] with sample equality
    rw [equality]
    exact zero_le_one.trans (le_max_left _ _)
  let weights (depth : ℕ) := (electricalComparisonWeight_memLp_two measure (sequence depth)
    (Lp.stronglyMeasurable (sequence depth)).measurable (inverseFourth depth)).toLp
      (fun sample => electricalComparisonWeight (sequence depth sample))
  have weightEquality (depth : ℕ) := MemLp.coeFn_toLp
    (electricalComparisonWeight_memLp_two measure (sequence depth) (Lp.stronglyMeasurable (sequence depth)).measurable (inverseFourth depth))
  have weightsBound (depth : ℕ) : ‖weights depth‖ ≤ Real.sqrt (1+bound) :=
    electricalComparisonWeight_norm_le measure (sequence depth) (Lp.stronglyMeasurable (sequence depth)).measurable
      (inverseFourth depth) bound (inverseBound depth)
  constructor
  · have comparison := lp2_weighted_positive_difference_tendsto_zero measure sequence limit convergence
      (fun _ => referenceWeight) (fun _ => referenceNonnegative) ‖referenceWeight‖ (fun _ => le_rfl)
    have integrals (depth : ℕ) : (∫ sample, max (sequence depth sample-limit sample) 0 * referenceWeight sample ∂measure) =
        ∫ sample, max (sequence depth sample-limit sample) 0 * max 1 ((limit sample)⁻¹^2) ∂measure := by
      apply integral_congr_ae
      filter_upwards [referenceEquality] with sample equality
      rw [equality]
      rfl
    simpa only [integrals] using comparison
  · apply squeeze_zero (g := fun depth => ‖sequence depth-limit‖ * Real.sqrt (1+bound))
    · intro depth
      exact integral_nonneg (fun sample => mul_nonneg (le_max_right _ _) (zero_le_one.trans (le_max_left _ _)))
    · intro depth
      have comparison := lp2_positive_weighted_difference_mean_le measure limit (sequence depth) (weights depth)
      have equality : (∫ sample, max (limit sample-sequence depth sample) 0 * weights depth sample ∂measure) =
          ∫ sample, max (limit sample-sequence depth sample) 0 * max 1 ((sequence depth sample)⁻¹^2) ∂measure := by
        apply integral_congr_ae
        filter_upwards [weightEquality depth] with sample equality
        rw [equality]
        rfl
      rw [equality, norm_sub_rev] at comparison
      exact comparison.trans (mul_le_mul_of_nonneg_left (weightsBound depth) (norm_nonneg _))
    · have normConvergence := (convergence.sub_const limit).norm
      simpa only [sub_self, norm_zero, zero_mul] using normConvergence.mul_const (Real.sqrt (1+bound))

theorem electrical_comparison_coefficients_tendsto_zero
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (sequencePositive : ∀ depth, ∀ᵐ sample ∂measure, 0 < sequence depth sample)
    (limitPositive : ∀ᵐ sample ∂measure, 0 < limit sample)
    (inverseFourth : ∀ depth, Integrable (fun sample => (sequence depth sample)⁻¹^4) measure)
    (limitInverseFourth : Integrable (fun sample => (limit sample)⁻¹^4) measure)
    (bound : ℝ) (inverseBound : ∀ depth, (∫ sample, (sequence depth sample)⁻¹^4 ∂measure) ≤ bound) :
    Tendsto (fun depth =>
      (∫ sample, max (sequence depth sample-limit sample) 0 * max 1 ((limit sample)⁻¹^2) ∂measure) /
        (∫ sample, min (limit sample) (limit sample)⁻¹ ∂measure)) atTop (𝓝 0) ∧
    Tendsto (fun depth =>
      (∫ sample, max (limit sample-sequence depth sample) 0 * max 1 ((sequence depth sample)⁻¹^2) ∂measure) /
        (∫ sample, min (sequence depth sample) (sequence depth sample)⁻¹ ∂measure)) atTop (𝓝 0) := by
  obtain ⟨forward, backward⟩ := electrical_comparison_numerators_tendsto_zero measure sequence limit convergence
    inverseFourth limitInverseFourth bound inverseBound
  have denominatorConvergence := electrical_comparison_denominator_tendsto measure sequence limit convergence sequencePositive limitPositive
  have denominatorPositive := electrical_comparison_denominator_mean_positive measure limit limitPositive
  exact ⟨by simpa only [zero_div] using forward.div_const _,
    by simpa only [Pi.div_def, zero_div] using backward.div denominatorConvergence denominatorPositive.ne'⟩

end
end IGSIII34.Probability


