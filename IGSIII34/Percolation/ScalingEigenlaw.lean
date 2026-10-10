import IGSIII34.Percolation.NormalizedLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

theorem scaledProbabilityLaw_comp (first second : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) :
    scaledProbabilityLaw first (scaledProbabilityLaw second law) = scaledProbabilityLaw (first * second) law := by
  apply Subtype.ext
  change (scaledProbabilityLaw first (scaledProbabilityLaw second law) : Measure ℝ≥0) =
    (scaledProbabilityLaw (first * second) law : Measure ℝ≥0)
  rw [scaledProbabilityLaw_measure, scaledProbabilityLaw_measure, scaledProbabilityLaw_measure,
    Measure.map_map (g := fun value : ℝ≥0 => first * value) (f := fun value : ℝ≥0 => second * value)
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)]
  congr 1
  funext value
  exact (mul_assoc first second value).symm

theorem scaledProbabilityLaw_one (law : ProbabilityMeasure ℝ≥0) : scaledProbabilityLaw 1 law = law := by
  apply Subtype.ext
  change (scaledProbabilityLaw 1 law : Measure ℝ≥0) = (law : Measure ℝ≥0)
  rw [scaledProbabilityLaw_measure]
  have multiplierIdentity : (fun value : ℝ≥0 => (1 : ℝ≥0) * value) = id := by
    funext value
    exact one_mul value
  rw [multiplierIdentity]
  exact Measure.map_id

theorem electrical_eigenlaw_scaling (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (eigenlaw : normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law) :
    electricalOutputLaw rule parameter positive belowOne fixedPoint law =
      scaledProbabilityLaw (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)) law := by
  have scalarPositive : 0 < Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law) :=
    Real.toNNReal_pos.mpr meanPositive
  have inverseEquality : Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ =
      (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law))⁻¹ := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr meanPositive.le), NNReal.coe_inv,
      Real.coe_toNNReal _ meanPositive.le]
  have scaled := congrArg
    (scaledProbabilityLaw (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law))) eigenlaw
  unfold normalizedElectricalLaw at scaled
  rw [inverseEquality, scaledProbabilityLaw_comp, mul_inv_cancel₀ scalarPositive.ne', scaledProbabilityLaw_one] at scaled
  exact scaled

end
end IGSIII34.Percolation
