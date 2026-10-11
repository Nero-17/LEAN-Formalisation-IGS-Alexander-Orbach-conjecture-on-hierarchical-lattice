import IGSIII34.Percolation.Continuation.ElectricalBoundaryTransferLimit
import IGSIII34.Percolation.ElectricalFixedLaw
import IGSIII34.Percolation.ElectricalNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

theorem electrical_eigenlaw_endogenous_fixed_function_exists (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    ∃ value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ,
      StronglyMeasurable value ∧ MemLp value 2 (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (independentInnovationLaw rule p positive belowOne fixedPoint).map value = (law:Measure ℝ≥0).map NNReal.toReal ∧
      value =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
        fun marks => (growth:ℝ)⁻¹*nonnegativeElectricalTransfer rule value marks := by
  obtain ⟨value, valueMeasurable, valueMemLp, fieldLaw, rawConvergence⟩ :=
    electrical_eigenlaw_endogenous_boundary_limit_with_law_exists rule p positive belowOne fixedPoint
      law lawPositive moments growth growthAboveOne eigenlaw
  have marksMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1) := by fun_prop
  have marksPreserving : MeasurePreserving (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ⟨marksMeasurable, electricalBoundaryInnovationLaw_marks_map rule p positive belowOne fixedPoint law⟩
  have secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_two] using moments 2
  letI : IsProbabilityMeasure ((law:Measure ℝ≥0).map NNReal.toReal) :=
    Measure.isProbabilityMeasure_map NNReal.continuous_coe.measurable.aemeasurable
  have realLawMemLp : MemLp (fun value : ℝ => value) 2 ((law:Measure ℝ≥0).map NNReal.toReal) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable NNReal.continuous_coe.measurable.aemeasurable).mpr
    simpa only [Function.comp_def, id_eq] using
      (memLp_two_iff_integrable_sq NNReal.continuous_coe.measurable.aestronglyMeasurable).mpr secondMoment
  have sequenceMeasurable (depth : ℕ) : Measurable (fun sample =>
      (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)) :=
    (NNReal.continuous_coe.measurable.comp (electricalBoundaryTreeIteration_measurable rule (depth+1))).div_const _
  have l1Convergence := electrical_constant_law_tendsto_eLpNorm_one
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) _ sequenceMeasurable
    ((law:Measure ℝ≥0).map NNReal.toReal) realLawMemLp
    (fun depth => electricalBoundaryTreeIteration_normalized_real_law rule p positive belowOne fixedPoint law growth
      (zero_lt_one.trans growthAboveOne) eigenlaw (depth+1))
    (fun sample => value (fun coordinate => (sample coordinate).1))
    (valueMemLp.comp_measurePreserving marksPreserving) rawConvergence
  have fixedMixed := electricalBoundaryNormalizedTransfer_fixed_of_raw_L1_limit rule p positive belowOne fixedPoint
    law growth (fun sample => value (fun coordinate => (sample coordinate).1))
    (valueMeasurable.measurable.comp marksMeasurable) l1Convergence
  have transferMeasurable : Measurable (nonnegativeElectricalTransfer rule value) :=
    (electricalCell_positivePart_dispatch_measurable rule.network).comp
      ((measurable_pi_apply ([], true)).prodMk
        (measurable_pi_lambda _ (fun edge => valueMeasurable.measurable.comp (innovationTreeShift_measurable rule [edge]))))
  have fixedOriginal : value =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => (growth:ℝ)⁻¹*nonnegativeElectricalTransfer rule value marks := by
    rw [← marksPreserving.map_eq]
    apply (ae_map_iff marksMeasurable.aemeasurable
      (measurableSet_eq_fun valueMeasurable.measurable (measurable_const.mul transferMeasurable))).mpr
    filter_upwards [fixedMixed] with sample fixed
    change value (fun coordinate => (sample coordinate).1) = (growth:ℝ)⁻¹ * electricalCell rule.network
      (sample ([], true)).1 (fun edge => max (value (fun coordinate =>
        (sample ([edge]++coordinate.1, coordinate.2)).1)) 0)
    simpa only [electricalBoundaryNormalizedTransfer, electricalBoundaryTreeShift] using fixed
  exact ⟨value, valueMeasurable, valueMemLp, fieldLaw, fixedOriginal⟩

theorem electrical_eigenlaw_endogenous_fixed_Lp_exists (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 (growth:ℝ) value = value ∧
      (independentInnovationLaw rule p positive belowOne fixedPoint).map value = (law:Measure ℝ≥0).map NNReal.toReal := by
  obtain ⟨value, valueMeasurable, valueMemLp, fieldLaw, fixedOriginal⟩ :=
    electrical_eigenlaw_endogenous_fixed_function_exists rule p positive belowOne fixedPoint law lawPositive
      moments growth growthAboveOne eigenlaw
  let endpoint := valueMemLp.toLp value
  have endpointEquality : (endpoint : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] value := valueMemLp.coeFn_toLp
  have congruence := nonnegativeElectricalTransfer_congr_ae rule p positive belowOne fixedPoint endpointEquality
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 (growth:ℝ) endpoint = endpoint := by
    unfold normalizedElectricalTransferLp
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (growth:ℝ)⁻¹ (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint 2 endpoint),
      nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 endpoint,
      congruence, fixedOriginal, endpointEquality] with marks scalar transfer congruence fixed endpoint
    simp only [scalar, Pi.smul_apply, smul_eq_mul, transfer, congruence, endpoint]
    exact fixed.symm
  exact ⟨endpoint, endpointFixed, (Measure.map_congr endpointEquality).trans fieldLaw⟩

end
end IGSIII34.Percolation
