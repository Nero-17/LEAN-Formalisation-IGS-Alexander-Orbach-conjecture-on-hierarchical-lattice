import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory

theorem condExp_scaled_positive_part_comparison
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (information : MeasurableSpace Sample)
    (first second scaledFirst scaledSecond : Sample → ℝ)
    (scalar coefficient : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (firstEquality : scaledFirst =ᵐ[measure] fun sample => scalar * first sample)
    (secondEquality : scaledSecond =ᵐ[measure] fun sample => scalar * second sample)
    (comparison : ∀ᵐ sample ∂measure,
      measure[fun sample => max (first sample-second sample) 0 | information] sample ≤
        coefficient * measure[second | information] sample) :
    ∀ᵐ sample ∂measure,
      measure[fun sample => max (scaledFirst sample-scaledSecond sample) 0 | information] sample ≤
        coefficient * measure[scaledSecond | information] sample := by
  have positivePartEquality : (fun sample => max (scaledFirst sample-scaledSecond sample) 0) =ᵐ[measure]
      scalar • (fun sample => max (first sample-second sample) 0) := by
    filter_upwards [firstEquality, secondEquality] with sample firstEqualityAt secondEqualityAt
    simp only [firstEqualityAt, secondEqualityAt, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub]
    simpa only [mul_zero] using (mul_max_of_nonneg (first sample-second sample) 0 scalarNonnegative).symm
  have firstConditional := condExp_congr_ae (m := information) positivePartEquality
  have secondConditional := condExp_congr_ae (m := information) secondEquality
  have firstScaling := condExp_smul (μ := measure) scalar (fun sample => max (first sample-second sample) 0) information
  have secondScaling := condExp_smul (μ := measure) scalar second information
  filter_upwards [firstConditional, secondConditional, firstScaling, secondScaling, comparison]
    with sample firstConditional secondConditional firstScaling secondScaling bound
  rw [firstConditional, firstScaling, secondConditional]
  change scalar * measure[fun sample => max (first sample-second sample) 0 | information] sample ≤
    coefficient * measure[scalar • second | information] sample
  rw [secondScaling, Pi.smul_apply, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left bound scalarNonnegative).trans_eq (by ring)

end
end IGSIII34.Probability

