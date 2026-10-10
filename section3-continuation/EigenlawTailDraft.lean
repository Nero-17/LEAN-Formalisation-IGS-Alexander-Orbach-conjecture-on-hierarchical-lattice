import IGSIII34.Percolation.PositiveEigenlaw
import IGSIII34.Probability.InverseMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

theorem normalized_electrical_eigenlaw_smallBall (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (eigenlaw : normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law)
    (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    (law : Measure ℝ≥0) {value | (value : ℝ) ≤ threshold} ≤
      ENNReal.ofReal (rule.network.reliability (parameter * ((law : Measure ℝ≥0)
        {value | (value : ℝ) ≤ ((rule.edges : ℝ) * electricalOutputMean rule parameter positive belowOne fixedPoint law) * threshold}).toReal) / parameter) := by
  have scaleEquality : (law : Measure ℝ≥0) {value | (value : ℝ) ≤ threshold} =
      (electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)
        {value | (value : ℝ) ≤ electricalOutputMean rule parameter positive belowOne fixedPoint law * threshold} := by
    calc
      _ = (normalizedElectricalLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)
          {value | (value : ℝ) ≤ threshold} :=
        (congrArg (fun result : ProbabilityMeasure ℝ≥0 => (result : Measure ℝ≥0)
          {value | (value : ℝ) ≤ threshold}) eigenlaw).symm
      _ = _ := by
        unfold normalizedElectricalLaw
        rw [scaledProbabilityLaw_measure, Measure.map_apply
          (f := fun value : ℝ≥0 => Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ * value)
          (measurable_const.mul measurable_id)
          (measurableSet_le NNReal.continuous_coe.measurable measurable_const)]
        congr 1
        ext value
        change ((Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ * value : ℝ≥0) : ℝ) ≤ threshold ↔ _
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr meanPositive.le), inv_mul_le_iff₀ meanPositive]
        rfl
  rw [scaleEquality]
  convert electricalOutputLaw_smallBall_le rule parameter positive belowOne fixedPoint law
    (electricalOutputMean rule parameter positive belowOne fixedPoint law * threshold)
    (mul_nonneg meanPositive.le thresholdNonnegative) using 1
  rw [mul_assoc]

theorem meanOneLaw_smallBall_below_one (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (threshold : ℝ) (thresholdBelowOne : threshold < 1) :
    (law : Measure ℝ≥0).real {value | (value : ℝ) ≤ threshold} < 1 := by
  have probabilityBound : (law : Measure ℝ≥0) {value | (value : ℝ) ≤ threshold} ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have realBound : (law : Measure ℝ≥0).real {value | (value : ℝ) ≤ threshold} ≤ 1 := by
    simpa only [Measure.real_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top probabilityBound
  apply lt_of_le_of_ne realBound
  intro equality
  have probabilityOne : (law : Measure ℝ≥0) {value | (value : ℝ) ≤ threshold} = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp equality
  have almostBound : ∀ᵐ value : ℝ≥0 ∂(law : Measure ℝ≥0), (value : ℝ) ≤ threshold := by
    have eventMeasurable : MeasurableSet {value : ℝ≥0 | (value : ℝ) ≤ threshold} :=
      measurableSet_le NNReal.continuous_coe.measurable measurable_const
    exact (mem_ae_iff_prob_eq_one (μ := (law : Measure ℝ≥0)) eventMeasurable).mpr probabilityOne
  have integrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0) :=
    Integrable.of_integral_ne_zero (by rw [meanOne]; exact one_ne_zero)
  have meanBound := integral_mono_ae integrable
    (integrable_const threshold : Integrable (fun _value : ℝ≥0 => threshold) (law : Measure ℝ≥0)) almostBound
  rw [meanOne, integral_const] at meanBound
  simp only [measureReal_univ_eq_one, one_smul] at meanBound
  linarith

end
end IGSIII34.Percolation
