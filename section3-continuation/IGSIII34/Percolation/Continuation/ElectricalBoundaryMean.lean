import IGSIII34.Percolation.Continuation.ElectricalBoundaryIndependence
import IGSIII34.Percolation.ElectricalConditionalUpper
import IGSIII34.Percolation.ElectricalFixedEnvelope
import IGSIII34.Percolation.PhysicalMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal

theorem electricalBoundaryTreeIteration_weighted_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (depth : ℕ) :
    (fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample : ℝ)) =ᵐ[
      electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
      fun sample => electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
        (fun leaf => positiveRepresentative (fun value : ℝ≥0 => (value:ℝ))
          (sample (generationEdgeAddress rule depth leaf, true)).2) := by
  have marksPreserving : MeasurePreserving (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ⟨measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)),
      electricalBoundaryInnovationLaw_marks_map rule p positive belowOne fixedPoint law⟩
  have crossing := marksPreserving.quasiMeasurePreserving.ae (independentInnovationLaw_crosses rule p positive belowOne fixedPoint)
  have boundaryPositive := ae_all_iff.mpr (fun address : List (Fin rule.edges) =>
    (electricalBoundaryInnovationLaw_boundary_preserving rule p positive belowOne fixedPoint law address).quasiMeasurePreserving.ae lawPositive)
  filter_upwards [crossing, boundaryPositive] with sample crossing positivity
  have weighted := electricalBoundaryTreeIteration_weighted_actual rule sample crossing positivity depth []
  have rootShift : electricalBoundaryTreeShift rule [] sample = sample := by funext coordinate; rfl
  rw [rootShift] at weighted
  rw [weighted]
  simp only [List.nil_append]
  congr 1
  funext leaf
  symm
  apply if_pos
  exact_mod_cast positivity (generationEdgeAddress rule depth leaf)

theorem electricalBoundaryTreeIteration_mean_sandwich (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (lawIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)) (law:Measure ℝ≥0))
    (inverseIntegrable : Integrable (fun value : ℝ≥0 => (value:ℝ)⁻¹) (law:Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value:ℝ) ∂(law:Measure ℝ≥0)) = 1) (depth : ℕ) :
    (electricalOrbitScale rule p positive belowOne fixedPoint (depth+1):ℝ) /
        (∫ value : ℝ≥0, (value:ℝ)⁻¹ ∂(law:Measure ℝ≥0)) ≤
      ∫ sample, (electricalBoundaryTreeIteration rule (depth+1) sample : ℝ)
        ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law ∧
      (∫ sample, (electricalBoundaryTreeIteration rule (depth+1) sample : ℝ)
        ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
        (electricalOrbitScale rule p positive belowOne fixedPoint (depth+1):ℝ) := by
  let measure := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law
  let configuration (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :=
    markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true
  let boundary (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0)
      (leaf : Fin (rule.generation depth).edges) := (sample (generationEdgeAddress rule depth leaf, true)).2
  let representative := positiveRepresentative (fun value : ℝ≥0 => (value:ℝ))
  have representativeMeasurable : Measurable representative := positiveRepresentative_measurable NNReal.continuous_coe.measurable
  have representativeEquality : representative =ᵐ[(law:Measure ℝ≥0)] (fun value : ℝ≥0 => (value:ℝ)) :=
    positiveRepresentative_ae_eq _ (lawPositive.mono (fun value positive => by exact_mod_cast positive))
  have representativeIntegrable := lawIntegrable.congr representativeEquality.symm
  have inverseEquality : (fun value => (representative value)⁻¹) =ᵐ[(law:Measure ℝ≥0)]
      (fun value : ℝ≥0 => (value:ℝ)⁻¹) := representativeEquality.fun_comp Inv.inv
  have inverseRepresentativeIntegrable := inverseIntegrable.congr inverseEquality.symm
  have configurationMeasurable : Measurable configuration :=
    (markedGenerationConfiguration_measurable rule depth [] true).comp
      (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))
  have boundaryMeasurable : Measurable boundary :=
    measurable_pi_lambda _ (fun leaf => measurable_snd.comp (measurable_pi_apply (generationEdgeAddress rule depth leaf, true)))
  letI : IsProbabilityMeasure (measure.map boundary) := Measure.isProbabilityMeasure_map boundaryMeasurable.aemeasurable
  have evaluationPreserving (leaf : Fin (rule.generation depth).edges) :
      MeasurePreserving (fun input : Fin (rule.generation depth).edges → ℝ≥0 => input leaf)
        (measure.map boundary) (law:Measure ℝ≥0) := by
    refine ⟨measurable_pi_apply leaf, ?_⟩
    rw [Measure.map_map (measurable_pi_apply leaf) boundaryMeasurable]
    exact (electricalBoundaryInnovationLaw_boundary_preserving rule p positive belowOne fixedPoint law
      (generationEdgeAddress rule depth leaf)).map_eq
  have inputIntegrable (leaf : Fin (rule.generation depth).edges) :=
    (evaluationPreserving leaf).integrable_comp_of_integrable representativeIntegrable
  have inverseInputIntegrable (leaf : Fin (rule.generation depth).edges) :=
    (evaluationPreserving leaf).integrable_comp_of_integrable inverseRepresentativeIntegrable
  have inputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ input, representative (input leaf) ∂measure.map boundary) = 1 := by
    have transport := integral_map_of_stronglyMeasurable (μ := measure.map boundary)
      (evaluationPreserving leaf).measurable representativeMeasurable.stronglyMeasurable
    rw [(evaluationPreserving leaf).map_eq] at transport
    exact transport.symm.trans ((integral_congr_ae representativeEquality).trans meanOne)
  have inverseInputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ input, (representative (input leaf))⁻¹ ∂measure.map boundary) =
        ∫ value : ℝ≥0, (value:ℝ)⁻¹ ∂(law:Measure ℝ≥0) := by
    have transport := integral_map_of_stronglyMeasurable (μ := measure.map boundary)
      (evaluationPreserving leaf).measurable representativeMeasurable.inv.stronglyMeasurable
    rw [(evaluationPreserving leaf).map_eq] at transport
    exact transport.symm.trans (integral_congr_ae inverseEquality)
  have inversePositive := inverse_mean_positive (law:Measure ℝ≥0) (fun value : ℝ≥0 => (value:ℝ))
    (lawPositive.mono (fun value positive => by exact_mod_cast positive)) inverseIntegrable
  have independent := electricalBoundaryTree_configuration_frontier_independent rule p positive belowOne fixedPoint law depth
  have lower := independent_conditional_electrical_mean_lower measure configuration boundary configurationMeasurable
    boundaryMeasurable independent (rule.generation depth).network id measurable_id
    (fun input leaf => representative (input leaf))
    (measurable_pi_lambda _ (fun leaf => representativeMeasurable.comp (measurable_pi_apply leaf)))
    (fun input leaf => positiveRepresentative_positive _ _) inputIntegrable inverseInputIntegrable _ inversePositive inverseInputMean
  have upper := independent_conditional_electrical_mean_upper measure configuration boundary configurationMeasurable
    boundaryMeasurable independent (rule.generation depth).network id measurable_id
    (fun input leaf => representative (input leaf))
    (measurable_pi_lambda _ (fun leaf => representativeMeasurable.comp (measurable_pi_apply leaf)))
    (fun input leaf => positiveRepresentative_positive _ _) inputIntegrable 1 zero_le_one inputMean
  have unitIntegrable : Integrable (fun sample => unitConfigurationResistance (rule.generation depth).network (configuration sample)) measure := by
    have finiteIntegral : Integrable (unitConfigurationResistance (rule.generation depth).network)
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks => markedGenerationConfiguration rule marks depth [] true)) := Integrable.of_finite
    exact (electricalBoundaryTree_configuration_preserving rule p positive belowOne fixedPoint law depth).integrable_comp_of_integrable finiteIntegral
  have unitMean : (∫ sample, unitConfigurationResistance (rule.generation depth).network (configuration sample) ∂measure) =
      (electricalOrbitScale rule p positive belowOne fixedPoint (depth+1):ℝ) := by
    have transport := integral_map_of_stronglyMeasurable (μ := measure)
      (electricalBoundaryTree_configuration_preserving rule p positive belowOne fixedPoint law depth).measurable
      (measurable_of_countable (unitConfigurationResistance (rule.generation depth).network)).stronglyMeasurable
    rw [(electricalBoundaryTree_configuration_preserving rule p positive belowOne fixedPoint law depth).map_eq] at transport
    rw [← transport,
      integral_map_of_stronglyMeasurable (markedGenerationConfiguration_measurable rule depth [] true)
        (measurable_of_countable _).stronglyMeasurable]
    rw [electricalOrbitScale_eq_actual_mean rule classical p positive belowOne fixedPoint]
    apply integral_congr_ae
    filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crossing
    exact markedGeneration_resistance_eq_iteration rule marks crossing depth []
  have responseEquality := electricalBoundaryTreeIteration_weighted_ae rule p positive belowOne fixedPoint law lawPositive depth
  have responseIntegrable : Integrable (fun sample => electricalCell (rule.generation depth).network
      (configuration sample) (fun leaf => representative (boundary sample leaf))) measure := by
    apply electricalCell_random_integrable measure (rule.generation depth).network configuration configurationMeasurable
      _ ((measurable_pi_lambda _ (fun leaf => representativeMeasurable.comp (measurable_pi_apply leaf))).comp boundaryMeasurable)
      (fun sample leaf => positiveRepresentative_positive _ _)
    intro leaf
    exact (electricalBoundaryInnovationLaw_boundary_preserving rule p positive belowOne fixedPoint law
      (generationEdgeAddress rule depth leaf)).integrable_comp_of_integrable representativeIntegrable
  have lowerIntegral := integral_mono_ae (unitIntegrable.div_const _) (integrable_condExp)
    lower
  have upperIntegral := integral_mono_ae (integrable_condExp) (unitIntegrable.const_mul 1) upper
  rw [integral_div, unitMean, integral_condExp configurationMeasurable.comap_le] at lowerIntegral
  rw [integral_const_mul, unitMean, integral_condExp configurationMeasurable.comap_le, one_mul] at upperIntegral
  have equality := integral_congr_ae responseEquality
  exact ⟨lowerIntegral.trans_eq equality.symm, equality.trans_le upperIntegral⟩

end
end IGSIII34.Percolation
