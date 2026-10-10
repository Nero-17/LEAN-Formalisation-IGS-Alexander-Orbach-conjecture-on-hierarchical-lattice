import IGSIII34.Percolation.ElectricalConditionalJensen
import IGSIII34.Percolation.ElectricalBoundaryIteration
import IGSIII34.Percolation.ElectricalPrefix
import IGSIII34.Probability.PrefixMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem actual_electrical_boundary_conditional_mean_lower (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      unitConfigurationResistance (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true) / inverseMean ≤
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks =>
        electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
  have representativeEquality := positiveRepresentative_ae_eq _ valuePositive
  have representativeMeasurable := positiveRepresentative_measurable (Lp.stronglyMeasurable value).measurable
  have representativeIntegrable : Integrable (positiveRepresentative value) (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ((Lp.memLp value).integrable (by norm_num)).congr representativeEquality.symm
  have inverseEquality : (fun marks => (positiveRepresentative value marks)⁻¹) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] (fun marks => (value marks)⁻¹) := by
    filter_upwards [representativeEquality] with marks equality
    rw [equality]
  have inverseRepresentativeIntegrable := inverseIntegrable.congr inverseEquality.symm
  have boundaryMeasurable : Measurable (fun marks (leaf : Fin (rule.generation depth).edges) =>
      innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) :=
    measurable_pi_lambda _ (fun leaf => innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf))
  have historyMeasurable : Measurable (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}) =>
      marks coordinate.val) := measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)
  have inputMeasurable : Measurable (fun children : Fin (rule.generation depth).edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => fun leaf => positiveRepresentative value (children leaf)) :=
    measurable_pi_lambda _ (fun leaf => representativeMeasurable.comp (measurable_pi_apply leaf))
  have inputIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun children : Fin (rule.generation depth).edges →
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => positiveRepresentative value (children leaf))
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
    apply (integrable_map_measure (representativeMeasurable.comp (measurable_pi_apply leaf)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mpr
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).integrable_comp_of_integrable representativeIntegrable
  have inverseInputIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun children : Fin (rule.generation depth).edges →
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => (positiveRepresentative value (children leaf))⁻¹)
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
    apply (integrable_map_measure (representativeMeasurable.inv.comp (measurable_pi_apply leaf)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mpr
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).integrable_comp_of_integrable inverseRepresentativeIntegrable
  have inverseInputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        (positiveRepresentative value (children leaf))⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) = inverseMean := by
    have boundaryIntegral : (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        (positiveRepresentative value (children leaf))⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
        ∫ marks, (positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))⁻¹
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable boundaryMeasurable
        (representativeMeasurable.inv.comp (measurable_pi_apply leaf)).stronglyMeasurable
    rw [boundaryIntegral]
    have shiftIntegral : (∫ marks, (positiveRepresentative value marks)⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (innovationTreeShift rule (generationEdgeAddress rule depth leaf))) =
        ∫ marks, (positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))⁻¹
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable
        (innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf)) representativeMeasurable.inv.stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).map_eq] at shiftIntegral
    exact shiftIntegral.symm.trans ((integral_congr_ae inverseEquality).trans inverseMeanEquality)
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)
  have conditional := independent_conditional_electrical_mean_lower
    (independentInnovationLaw rule p positive belowOne fixedPoint) _ _ historyMeasurable boundaryMeasurable independent
    (rule.generation depth).network
    (fun data => markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) data) depth [] true)
    ((markedGenerationConfiguration_measurable rule depth [] true).comp (innovationPrefixFill_measurable rule (depth+1)))
    _ inputMeasurable (fun children leaf => positiveRepresentative_positive value (children leaf))
    inputIntegrable inverseInputIntegrable inverseMean inverseMeanPositive inverseInputMean
  rw [coordinatePrefixFiltration_eq_comap]
  simpa only [markedGenerationConfiguration_prefix_factor] using conditional

theorem normalized_electrical_boundary_conditional_mean_lower (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (growth⁻¹)^(depth+1)*unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) / inverseMean ≤
      (independentInnovationLaw rule p positive belowOne fixedPoint)[
        ⇑((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] value) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
  have weighted := normalizedElectricalTransferLp_iterate_weighted_actual_ae rule p positive belowOne fixedPoint
    growth growthNonnegative value valuePositive depth
  have conditionalEquality := condExp_congr_ae (m := coordinatePrefixFiltration
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)) weighted
  have scalarEquality := condExp_smul (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
    ((growth⁻¹)^(depth+1))
    (fun marks => electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)))
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
  have lower := actual_electrical_boundary_conditional_mean_lower rule p positive belowOne fixedPoint value valuePositive
    inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  filter_upwards [conditionalEquality, scalarEquality, lower] with marks conditional scalar inequality
  rw [conditional]
  change _ ≤ (independentInnovationLaw rule p positive belowOne fixedPoint)[((growth⁻¹)^(depth+1)) •
    (fun marks => electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))) |
      coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks
  rw [scalar, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (growth⁻¹)^(depth+1)*(unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)/inverseMean) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left inequality (pow_nonneg (inv_nonneg.mpr growthNonnegative) _)

end
end IGSIII34.Percolation

