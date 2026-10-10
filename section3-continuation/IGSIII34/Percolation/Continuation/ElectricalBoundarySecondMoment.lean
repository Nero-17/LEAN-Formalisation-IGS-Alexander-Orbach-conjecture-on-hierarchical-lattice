import IGSIII34.Percolation.Continuation.ElectricalBoundaryProductLaw
import IGSIII34.Percolation.Continuation.ElectricalBoundaryMean
import IGSIII34.Percolation.OutputMoments
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal BigOperators

theorem electricalCell_nnreal_square_integrable {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (law : ProbabilityMeasure ℝ≥0)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0)) :
    Integrable (fun input : Fin edges → ℝ≥0 =>
      electricalCell network configuration (fun edge => (input edge:ℝ))^2)
      (Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) := by
  have domination : Integrable (fun input : Fin edges → ℝ≥0 =>
      (edges:ℝ)*∑ edge, (input edge:ℝ)^2)
      (Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0))) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro edge _
    exact (measurePreserving_eval (fun _ : Fin edges => (law:Measure ℝ≥0)) edge).integrable_comp_of_integrable secondMoment
  have measurable : Measurable (fun input : Fin edges → ℝ≥0 =>
      electricalCell network configuration (fun edge => (input edge:ℝ))^2) :=
    (NNReal.continuous_coe.comp (electricalCellNNReal_continuous network configuration)).measurable.pow_const 2
  apply domination.mono' measurable.aestronglyMeasurable
  filter_upwards [] with input
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact_mod_cast electricalCellNNReal_secondMoment_bound network configuration input

theorem electricalCell_nnreal_product_square_integrable {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (configurationLaw : Measure (Configuration edges)) [IsProbabilityMeasure configurationLaw]
    (law : ProbabilityMeasure ℝ≥0)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0)) :
    Integrable (fun data : Configuration edges × (Fin edges → ℝ≥0) =>
      electricalCell network data.1 (fun edge => (data.2 edge:ℝ))^2)
      (configurationLaw.prod (Measure.pi (fun _ : Fin edges => (law:Measure ℝ≥0)))) := by
  have measurable : Measurable (fun data : Configuration edges × (Fin edges → ℝ≥0) =>
      electricalCell network data.1 (fun edge => (data.2 edge:ℝ))^2) :=
    (NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous network)).measurable.pow_const 2
  apply (integrable_prod_iff measurable.aestronglyMeasurable).mpr
  exact ⟨Filter.Eventually.of_forall (fun configuration =>
    electricalCell_nnreal_square_integrable network configuration law secondMoment), Integrable.of_finite⟩

theorem electricalBoundaryTreeIteration_weighted_coe_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (depth : ℕ) :
    (fun sample => (electricalBoundaryTreeIteration rule (depth+1) sample:ℝ)) =ᵐ[
      electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
      fun sample => electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
        (fun leaf => ((sample (generationEdgeAddress rule depth leaf, true)).2:ℝ)) := by
  have crossing := (show MeasurePreserving (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => fun coordinate => (sample coordinate).1)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      (independentInnovationLaw rule p positive belowOne fixedPoint) from
    ⟨measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)),
      electricalBoundaryInnovationLaw_marks_map rule p positive belowOne fixedPoint law⟩).quasiMeasurePreserving.ae
        (independentInnovationLaw_crosses rule p positive belowOne fixedPoint)
  have boundaryPositive := ae_all_iff.mpr (fun address : List (Fin rule.edges) =>
    (electricalBoundaryInnovationLaw_boundary_preserving rule p positive belowOne fixedPoint law address).quasiMeasurePreserving.ae lawPositive)
  filter_upwards [crossing, boundaryPositive] with sample crossing positivity
  have weighted := electricalBoundaryTreeIteration_weighted_actual rule sample crossing positivity depth []
  have rootShift : electricalBoundaryTreeShift rule [] sample = sample := by funext coordinate; rfl
  rw [rootShift] at weighted
  simpa only [List.nil_append] using weighted

theorem electricalBoundaryTreeIteration_eigenlaw_second_moment (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (∫ sample, (electricalBoundaryTreeIteration rule depth sample:ℝ)^2
      ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) =
      (growth:ℝ)^(2*depth)*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) := by
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    (electricalBoundaryTreeIteration_measurable rule depth)
    (NNReal.continuous_coe.measurable.pow_const 2).stronglyMeasurable
  rw [electricalBoundaryTreeIteration_law, electricalOutputLaw_iterate_eigenlaw rule p positive belowOne fixedPoint law growth eigenlaw depth,
    scaledProbabilityLaw_measure, integral_map_of_stronglyMeasurable
      (show Measurable (fun value : ℝ≥0 => growth^depth*value) from measurable_const.mul measurable_id)
      (NNReal.continuous_coe.measurable.pow_const 2).stronglyMeasurable] at transport
  simpa only [NNReal.coe_mul, NNReal.coe_pow, mul_pow, integral_const_mul, ← pow_mul, Nat.mul_comm] using transport.symm

theorem electricalBoundaryTree_eigenlaw_generation_second_moment (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    (∫ configuration, ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
      electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))^2
        ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))
        ∂((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks => markedGenerationConfiguration rule marks depth [] true))) =
      (growth:ℝ)^(2*(depth+1))*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) := by
  let configurationLaw := (independentInnovationLaw rule p positive belowOne fixedPoint).map
    (fun marks => markedGenerationConfiguration rule marks depth [] true)
  letI : IsProbabilityMeasure configurationLaw := Measure.isProbabilityMeasure_map
    (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
  have productIntegrable := electricalCell_nnreal_product_square_integrable
    (rule.generation depth).network configurationLaw law secondMoment
  rw [← integral_prod _ productIntegrable]
  have jointMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true,
        fun leaf : Fin (rule.generation depth).edges =>
          (sample (generationEdgeAddress rule depth leaf, true)).2)) :=
    ((markedGenerationConfiguration_measurable rule depth [] true).comp
      (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))).prodMk
      (measurable_pi_lambda _ (fun leaf => measurable_snd.comp
        (measurable_pi_apply (generationEdgeAddress rule depth leaf, true))))
  have responseMeasurable : Measurable (fun data :
      Configuration (rule.generation depth).edges × (Fin (rule.generation depth).edges → ℝ≥0) =>
      electricalCell (rule.generation depth).network data.1 (fun edge => (data.2 edge:ℝ))^2) :=
    (NNReal.continuous_coe.comp (electricalCellNNReal_joint_continuous (rule.generation depth).network)).measurable.pow_const 2
  have transport := integral_map_of_stronglyMeasurable
    (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    jointMeasurable responseMeasurable.stronglyMeasurable
  rw [electricalBoundaryTree_configuration_frontier_map] at transport
  rw [transport]
  have equality := (electricalBoundaryTreeIteration_weighted_coe_ae rule p positive belowOne fixedPoint law lawPositive depth).fun_comp
    (fun value : ℝ => value^2)
  exact (integral_congr_ae equality.symm).trans
    (electricalBoundaryTreeIteration_eigenlaw_second_moment rule p positive belowOne fixedPoint law growth eigenlaw (depth+1))

end
end IGSIII34.Percolation
