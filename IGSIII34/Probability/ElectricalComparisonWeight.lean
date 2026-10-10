import IGSIII34.Probability.LpWeightedDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped ENNReal _root_.Topology

def electricalComparisonWeight (value : ℝ) : ℝ := max 1 (value⁻¹^2)

theorem electricalComparisonWeight_measurable : Measurable electricalComparisonWeight :=
  measurable_const.max (measurable_id.inv.pow_const 2)

theorem electricalComparisonWeight_square_le (value : ℝ) :
    electricalComparisonWeight value^2 ≤ 1 + value⁻¹^4 := by
  unfold electricalComparisonWeight
  by_cases small : value⁻¹^2 ≤ 1
  · rw [max_eq_left small]
    nlinarith [sq_nonneg (value⁻¹^2)]
  · rw [max_eq_right (le_of_not_ge small)]
    nlinarith [sq_nonneg (value⁻¹^2)]

theorem electricalComparisonWeight_memLp_two
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (value : Sample → ℝ) (measurable : Measurable value)
    (inverseFourth : Integrable (fun sample => (value sample)⁻¹^4) measure) :
    MemLp (fun sample => electricalComparisonWeight (value sample)) 2 measure := by
  apply (memLp_two_iff_integrable_sq (electricalComparisonWeight_measurable.comp measurable).aestronglyMeasurable).mpr
  apply ((integrable_const (1 : ℝ)).add inverseFourth).mono'
    ((electricalComparisonWeight_measurable.comp measurable).pow_const 2).aestronglyMeasurable
  filter_upwards [] with sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact electricalComparisonWeight_square_le _

theorem electricalComparisonWeight_norm_le
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Sample → ℝ) (measurable : Measurable value)
    (inverseFourth : Integrable (fun sample => (value sample)⁻¹^4) measure)
    (bound : ℝ) (inverseBound : (∫ sample, (value sample)⁻¹^4 ∂measure) ≤ bound) :
    ‖(electricalComparisonWeight_memLp_two measure value measurable inverseFourth).toLp
      (fun sample => electricalComparisonWeight (value sample))‖ ≤ Real.sqrt (1+bound) := by
  have squareIntegral : (∫ sample, electricalComparisonWeight (value sample)^2 ∂measure) ≤ 1+bound := by
    have comparison := integral_mono
      (electricalComparisonWeight_memLp_two measure value measurable inverseFourth).integrable_sq
      ((integrable_const (1 : ℝ)).add inverseFourth) (fun sample => electricalComparisonWeight_square_le _)
    simp only [Pi.add_apply] at comparison
    rw [integral_add (integrable_const _) inverseFourth] at comparison
    simp only [integral_const, measureReal_univ_eq_one, one_smul] at comparison
    linarith
  have normSquare : ‖(electricalComparisonWeight_memLp_two measure value measurable inverseFourth).toLp
      (fun sample => electricalComparisonWeight (value sample))‖^2 =
      ∫ sample, electricalComparisonWeight (value sample)^2 ∂measure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (electricalComparisonWeight_memLp_two measure value measurable inverseFourth)]
      with sample equality
    rw [equality]
    change electricalComparisonWeight (value sample)*electricalComparisonWeight (value sample) = _
    ring
  exact Real.le_sqrt_of_sq_le (normSquare ▸ squareIntegral)

theorem electricalComparison_numerator_integrable
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (first second : Lp ℝ 2 measure)
    (inverseFourth : Integrable (fun sample => (second sample)⁻¹^4) measure) :
    Integrable (fun sample => max (first sample-second sample) 0 * max 1 ((second sample)⁻¹^2)) measure := by
  exact (((Lp.memLp first).sub (Lp.memLp second)).sup (memLp_const (0 : ℝ))).integrable_mul
    (electricalComparisonWeight_memLp_two measure second (Lp.stronglyMeasurable second).measurable inverseFourth)

end
end IGSIII34.Probability


