import IGSIII34.Percolation.Continuation.ElectricalBoundaryErrorConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

theorem electrical_integral_bounded_continuous_tendsto_of_tendstoInMeasure
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (sequence : ℕ → Sample → ℝ) (value : Sample → ℝ)
    (measurable : ∀ depth, AEStronglyMeasurable (sequence depth) measure)
    (convergence : TendstoInMeasure measure sequence atTop value) (test : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun depth => ∫ sample, test (sequence depth sample) ∂measure) atTop
      (𝓝 (∫ sample, test (value sample) ∂measure)) := by
  apply tendsto_of_subseq_tendsto
  intro subsequence indicesTendsto
  obtain ⟨subsubsequence, _, pointwise⟩ := (convergence.comp indicesTendsto).exists_seq_tendsto_ae
  refine ⟨subsubsequence, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
    (fun depth => test.continuous.comp_aestronglyMeasurable (measurable _))
    (integrable_const ‖test‖) (fun depth => Eventually.of_forall (fun sample => test.norm_coe_le_norm _))
  filter_upwards [pointwise] with sample pointwise
  exact test.continuous.continuousAt.tendsto.comp pointwise

theorem electrical_constant_law_tendstoInMeasure_limit_law
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Sample → ℝ) (value : Sample → ℝ)
    (measurable : ∀ depth, Measurable (sequence depth)) (valueMeasurable : Measurable value)
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (sequenceLaw : ∀ depth, measure.map (sequence depth) = law)
    (convergence : TendstoInMeasure measure sequence atTop value) : measure.map value = law := by
  letI : IsProbabilityMeasure (measure.map value) := Measure.isProbabilityMeasure_map valueMeasurable.aemeasurable
  have equality : (⟨measure.map value, inferInstance⟩ : FiniteMeasure ℝ) = ⟨law, inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro test
    simp only [FiniteMeasure.toMeasure_mk]
    have limit := electrical_integral_bounded_continuous_tendsto_of_tendstoInMeasure measure sequence value
      (fun depth => (measurable depth).aestronglyMeasurable) convergence test
    have integralEquality (depth : ℕ) : (∫ sample, test (sequence depth sample) ∂measure) = ∫ value, test value ∂law := by
      rw [← sequenceLaw depth, integral_map_of_stronglyMeasurable (measurable depth) test.continuous.measurable.stronglyMeasurable]
    simp_rw [integralEquality] at limit
    change (∫ value, test value ∂measure.map value) = ∫ value, test value ∂law
    rw [integral_map_of_stronglyMeasurable valueMeasurable test.continuous.measurable.stronglyMeasurable]
    exact tendsto_nhds_unique limit tendsto_const_nhds
  exact congrArg (fun law : FiniteMeasure ℝ => (law:Measure ℝ)) equality

theorem electricalBoundaryTreeIteration_normalized_real_law (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample => (electricalBoundaryTreeIteration rule depth sample:ℝ)/(growth:ℝ)^depth) =
      (law:Measure ℝ≥0).map NNReal.toReal := by
  have transported := congrArg (fun measure : Measure ℝ≥0 => measure.map NNReal.toReal)
    (electricalBoundaryTreeIteration_normalized_eigenlaw rule p positive belowOne fixedPoint law growth growthPositive eigenlaw depth)
  rw [Measure.map_map
    (f := fun sample => (growth^depth)⁻¹*electricalBoundaryTreeIteration rule depth sample)
    (g := NNReal.toReal) NNReal.continuous_coe.measurable
    (measurable_const.mul (electricalBoundaryTreeIteration_measurable rule depth))] at transported
  simpa only [Function.comp_def, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, div_eq_mul_inv, mul_comm] using transported

theorem electrical_eigenlaw_endogenous_boundary_limit_with_law_exists (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthAboveOne : 1 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    ∃ value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ,
      StronglyMeasurable value ∧ MemLp value 2 (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (independentInnovationLaw rule p positive belowOne fixedPoint).map value = (law:Measure ℝ≥0).map NNReal.toReal ∧
      TendstoInMeasure (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
        (fun depth sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)) atTop
        (fun sample => value (fun coordinate => (sample coordinate).1)) := by
  have secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_two] using moments 2
  have growthPositive := zero_lt_one.trans growthAboveOne
  obtain ⟨value, valueMeasurable, valueMemLp, meanConvergence⟩ := electrical_eigenlaw_endogenous_boundary_limit_exists
    rule p positive belowOne fixedPoint law lawPositive secondMoment growth growthPositive eigenlaw
  have sequenceMeasurable (depth : ℕ) : Measurable (fun sample =>
      (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)/(growth:ℝ)^(depth+1)) :=
    (NNReal.continuous_coe.measurable.comp (electricalBoundaryTreeIteration_measurable rule (depth+1))).div_const _
  have rawConvergence := electrical_tendstoInMeasure_of_centered_and_ae_limit
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) _ _ _
    (fun depth => (sequenceMeasurable depth).aestronglyMeasurable)
    (electricalBoundaryTreeIteration_centered_tendstoInMeasure_zero rule p positive belowOne fixedPoint
      law lawPositive moments growth growthAboveOne eigenlaw) meanConvergence
  have marksMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1) := by fun_prop
  letI : IsProbabilityMeasure ((law:Measure ℝ≥0).map NNReal.toReal) :=
    Measure.isProbabilityMeasure_map NNReal.continuous_coe.measurable.aemeasurable
  have fieldLaw := electrical_constant_law_tendstoInMeasure_limit_law
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) _ _ sequenceMeasurable
    (valueMeasurable.measurable.comp marksMeasurable) ((law:Measure ℝ≥0).map NNReal.toReal)
    (fun depth => electricalBoundaryTreeIteration_normalized_real_law rule p positive belowOne fixedPoint
      law growth growthPositive eigenlaw (depth+1)) rawConvergence
  change (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
    (value ∘ (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate => (sample coordinate).1)) = _ at fieldLaw
  rw [← Measure.map_map valueMeasurable.measurable marksMeasurable, electricalBoundaryInnovationLaw_marks_map] at fieldLaw
  exact ⟨value, valueMeasurable, valueMemLp, fieldLaw, rawConvergence⟩

end
end IGSIII34.Percolation
