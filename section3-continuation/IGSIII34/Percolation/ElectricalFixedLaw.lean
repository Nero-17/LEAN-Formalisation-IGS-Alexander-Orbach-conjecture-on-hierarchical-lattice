import IGSIII34.Percolation.ElectricalFieldMoments
import IGSIII34.Percolation.TreeLaw
import IGSIII34.Percolation.ScalingEigenlaw
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

def electricalFixedLaw (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) : ProbabilityMeasure ℝ≥0 :=
  ProbabilityMeasure.map (⟨independentInnovationLaw rule p positive belowOne fixedPoint, inferInstance⟩ : ProbabilityMeasure _)
    ((Lp.stronglyMeasurable value).measurable.real_toNNReal.aemeasurable)

theorem electricalFixedLaw_measure (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    (electricalFixedLaw rule p positive belowOne fixedPoint value : Measure ℝ≥0) =
      (independentInnovationLaw rule p positive belowOne fixedPoint).map (fun marks => Real.toNNReal (value marks)) := rfl

theorem electricalFixedLaw_mean_one (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1) :
    (∫ sample : ℝ≥0, (sample : ℝ) ∂(electricalFixedLaw rule p positive belowOne fixedPoint value : Measure ℝ≥0)) = 1 := by
  rw [electricalFixedLaw_measure, integral_map_of_stronglyMeasurable
    (Lp.stronglyMeasurable value).measurable.real_toNNReal NNReal.continuous_coe.measurable.stronglyMeasurable]
  apply Eq.trans _ meanOne
  apply integral_congr_ae
  filter_upwards [valuePositive] with marks valueStrict
  exact Real.coe_toNNReal _ valueStrict.le

theorem electricalFixedLaw_positive_ae (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) :
    ∀ᵐ sample ∂(electricalFixedLaw rule p positive belowOne fixedPoint value : Measure ℝ≥0), 0 < sample := by
  rw [electricalFixedLaw_measure]
  apply (ae_map_iff (Lp.stronglyMeasurable value).measurable.real_toNNReal.aemeasurable
    (measurableSet_lt measurable_const measurable_id)).mpr
  exact valuePositive.mono (fun _ valueStrict => Real.toNNReal_pos.mpr valueStrict)

theorem electricalFixedLaw_output_scaling (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    electricalOutputLaw rule p positive belowOne fixedPoint (electricalFixedLaw rule p positive belowOne fixedPoint value) =
      scaledProbabilityLaw (Real.toNNReal growth) (electricalFixedLaw rule p positive belowOne fixedPoint value) := by
  have stationary := electricalField_stationary_of_fixed rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed
  have fieldPositive := electricalField_positive rule p positive belowOne fixedPoint value valuePositive
  have rootScale : (fun marks => electricalCellNNReal rule.network (marks ([], true))
      (fun edge => Real.toNNReal (value (innovationTreeShift rule [edge] marks)))) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => Real.toNNReal growth*Real.toNNReal (value marks)) := by
    filter_upwards [stationary, fieldPositive, valuePositive] with marks recursion positivity rootPositive
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ growthPositive.le, Real.coe_toNNReal _ rootPositive.le]
    change electricalCell rule.network (marks ([], true))
      (fun edge => (Real.toNNReal (value (innovationTreeShift rule [edge] marks)) : ℝ)) = growth*value marks
    have clipping (edge : Fin rule.edges) :
        (Real.toNNReal (value (innovationTreeShift rule [edge] marks)) : ℝ) = value (innovationTreeShift rule [edge] marks) :=
      Real.coe_toNNReal _ (positivity [edge]).le
    simp_rw [clipping]
    have rootShift : innovationTreeShift rule [] marks = marks := by funext coordinate; rfl
    simpa only [electricalField, rootShift, List.nil_append] using recursion []
  apply Subtype.ext
  have law := innovationTree_electrical_law rule p positive belowOne fixedPoint
    (fun marks => Real.toNNReal (value marks)) (Lp.stronglyMeasurable value).measurable.real_toNNReal
    (electricalFixedLaw rule p positive belowOne fixedPoint value) rfl
  change (electricalOutputLaw rule p positive belowOne fixedPoint (electricalFixedLaw rule p positive belowOne fixedPoint value) : Measure ℝ≥0) =
    (scaledProbabilityLaw (Real.toNNReal growth) (electricalFixedLaw rule p positive belowOne fixedPoint value) : Measure ℝ≥0)
  rw [← law, scaledProbabilityLaw_measure, electricalFixedLaw_measure,
    Measure.map_map (g := fun sample : ℝ≥0 => Real.toNNReal growth*sample)
      (f := fun marks => Real.toNNReal (value marks)) (measurable_const.mul measurable_id)
      (Lp.stronglyMeasurable value).measurable.real_toNNReal]
  exact Measure.map_congr rootScale

theorem electricalFixedLaw_all_real_moments (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (moments : ∀ exponent : ℝ, Integrable (fun marks => (value marks)^exponent)
      (independentInnovationLaw rule p positive belowOne fixedPoint)) (exponent : ℝ) :
    Integrable (fun sample : ℝ≥0 => (sample : ℝ)^exponent)
      (electricalFixedLaw rule p positive belowOne fixedPoint value : Measure ℝ≥0) := by
  rw [electricalFixedLaw_measure]
  apply (integrable_map_measure (NNReal.continuous_coe.measurable.pow_const exponent).aestronglyMeasurable
    (Lp.stronglyMeasurable value).measurable.real_toNNReal.aemeasurable).mpr
  apply (moments exponent).congr
  filter_upwards [valuePositive] with marks valueStrict
  change (value marks)^exponent = ((Real.toNNReal (value marks) : ℝ≥0) : ℝ)^exponent
  rw [Real.coe_toNNReal _ valueStrict.le]

theorem electricalFixedLaw_output_mean (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    electricalOutputMean rule p positive belowOne fixedPoint (electricalFixedLaw rule p positive belowOne fixedPoint value) = growth := by
  unfold electricalOutputMean
  rw [electricalFixedLaw_output_scaling rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed,
    scaledProbabilityLaw_mean, electricalFixedLaw_mean_one rule p positive belowOne fixedPoint value valuePositive meanOne,
    mul_one, Real.coe_toNNReal _ growthPositive.le]

theorem electricalFixedLaw_normalized_fixed (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    normalizedElectricalLaw rule p positive belowOne fixedPoint (electricalFixedLaw rule p positive belowOne fixedPoint value) =
      electricalFixedLaw rule p positive belowOne fixedPoint value := by
  unfold normalizedElectricalLaw
  rw [electricalFixedLaw_output_mean rule p positive belowOne fixedPoint growth growthPositive value valuePositive meanOne fixed,
    electricalFixedLaw_output_scaling rule p positive belowOne fixedPoint growth growthPositive value valuePositive fixed,
    scaledProbabilityLaw_comp]
  have scalars : Real.toNNReal growth⁻¹*Real.toNNReal growth = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr growthPositive.le), Real.coe_toNNReal _ growthPositive.le,
      inv_mul_cancel₀ growthPositive.ne', NNReal.coe_one]
  rw [scalars, scaledProbabilityLaw_one]

theorem exists_electrical_eigenlaw_at_actual_growth
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) ∧
      ∃ law : ProbabilityMeasure ℝ≥0,
        (∫ sample : ℝ≥0, (sample : ℝ) ∂(law : Measure ℝ≥0)) = 1 ∧
        (∀ᵐ sample ∂(law : Measure ℝ≥0), 0 < sample) ∧
        (∀ exponent : ℝ, Integrable (fun sample : ℝ≥0 => (sample : ℝ)^exponent) (law : Measure ℝ≥0)) ∧
        electricalOutputMean rule p positive belowOne fixedPoint law = growth ∧
        normalizedElectricalLaw rule p positive belowOne fixedPoint law = law := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    value, valueFixed, valuePositive, valueMeanOne, valueMoments, _, _, _⟩ :=
      exists_actual_positive_endogenous_electrical_field_all_real_moments rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    electricalFixedLaw rule p positive belowOne fixedPoint value, ?_, ?_, ?_, ?_, ?_⟩
  · exact electricalFixedLaw_mean_one rule p positive belowOne fixedPoint value valuePositive valueMeanOne
  · exact electricalFixedLaw_positive_ae rule p positive belowOne fixedPoint value valuePositive
  · exact electricalFixedLaw_all_real_moments rule p positive belowOne fixedPoint value valuePositive valueMoments
  · exact electricalFixedLaw_output_mean rule p positive belowOne fixedPoint growth growthPositive value valuePositive valueMeanOne valueFixed
  · exact electricalFixedLaw_normalized_fixed rule p positive belowOne fixedPoint growth growthPositive value valuePositive valueMeanOne valueFixed

end
end IGSIII34.Percolation
