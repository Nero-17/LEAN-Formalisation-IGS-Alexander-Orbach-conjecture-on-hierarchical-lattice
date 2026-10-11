import IGSIII4.TransferLaw
import IGSIII34.Percolation.SmallBallLaw
import IGSIII34.Probability.InverseMoments

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation
open scoped NNReal ENNReal

theorem supersolution_smallBall_recursion (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) {factor threshold : ℝ}
    (factorPositive : 0 < factor) (thresholdNonnegative : 0 ≤ threshold)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      (electricalTransferNNReal rule value marks : ℝ) ≤ factor * (value marks : ℝ)) :
    (independentInnovationLaw rule probability positive belowOne fixedPoint).real
      {marks | (value marks : ℝ) ≤ threshold} ≤
    IGSIII34.Probability.thinningMap rule.network probability
      ((independentInnovationLaw rule probability positive belowOne fixedPoint).real
        {marks | (value marks : ℝ) ≤ (rule.edges : ℝ) * factor * threshold}) := by
  have eventMeasurable (bound : ℝ) : MeasurableSet {value : ℝ≥0 | (value : ℝ) ≤ bound} :=
    measurableSet_le NNReal.continuous_coe.measurable measurable_const
  have outputBound := electricalOutputLaw_smallBall_le rule probability positive belowOne fixedPoint
    (innovationValueLaw rule probability positive belowOne fixedPoint value measurable)
    (factor * threshold) (mul_nonneg factorPositive.le thresholdNonnegative)
  rw [← electricalTransferNNReal_law rule probability positive belowOne fixedPoint value measurable,
    Measure.map_apply (electricalTransferNNReal_measurable rule value measurable)
      (eventMeasurable (factor * threshold))] at outputBound
  have eventBound :
      (independentInnovationLaw rule probability positive belowOne fixedPoint)
        {marks | (value marks : ℝ) ≤ threshold} ≤
      (independentInnovationLaw rule probability positive belowOne fixedPoint)
        {marks | (electricalTransferNNReal rule value marks : ℝ) ≤ factor * threshold} := by
    apply measure_mono_ae
    filter_upwards [supersolution] with marks comparison small
    exact comparison.trans (mul_le_mul_of_nonneg_left small factorPositive.le)
  have inputLawBound :
      ((innovationValueLaw rule probability positive belowOne fixedPoint value measurable : Measure ℝ≥0)
        {value | (value : ℝ) ≤ (rule.edges : ℝ) * (factor * threshold)}).toReal =
      (independentInnovationLaw rule probability positive belowOne fixedPoint).real
        {marks | (value marks : ℝ) ≤ (rule.edges : ℝ) * factor * threshold} := by
    change (((independentInnovationLaw rule probability positive belowOne fixedPoint).map value)
      {value | (value : ℝ) ≤ (rule.edges : ℝ) * (factor * threshold)}).toReal = _
    rw [Measure.map_apply measurable (eventMeasurable _)]
    simp only [Measure.real, mul_assoc]
    rfl
  rw [inputLawBound] at outputBound
  have combined := eventBound.trans outputBound
  have thinningNonnegative : 0 ≤ IGSIII34.Probability.thinningMap rule.network probability
      ((independentInnovationLaw rule probability positive belowOne fixedPoint).real
        {marks | (value marks : ℝ) ≤ (rule.edges : ℝ) * factor * threshold}) :=
    IGSIII34.Probability.thinningMap_nonnegative rule.network positive belowOne
      measureReal_nonneg measureReal_le_one
  have realBound := ENNReal.toReal_mono (by simp) combined
  change _ ≤ (ENNReal.ofReal (IGSIII34.Probability.thinningMap rule.network probability
      ((independentInnovationLaw rule probability positive belowOne fixedPoint).real
        {marks | (value marks : ℝ) ≤ (rule.edges : ℝ) * factor * threshold}))).toReal at realBound
  rwa [ENNReal.toReal_ofReal thinningNonnegative] at realBound

end
end IGSIII4
