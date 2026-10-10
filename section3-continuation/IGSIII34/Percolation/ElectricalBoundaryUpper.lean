import IGSIII34.Percolation.ElectricalConditionalUpper
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

theorem actual_electrical_boundary_conditional_mean_upper (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (mean : ℝ) (meanNonnegative : 0 ≤ mean)
    (meanEquality : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = mean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks =>
        electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
        mean * unitConfigurationResistance (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true) := by
  have representativeEquality := positiveRepresentative_ae_eq _ valuePositive
  have representativeMeasurable := positiveRepresentative_measurable (Lp.stronglyMeasurable value).measurable
  have representativeIntegrable : Integrable (positiveRepresentative value) (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ((Lp.memLp value).integrable (by norm_num)).congr representativeEquality.symm
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
  have inputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        positiveRepresentative value (children leaf)
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) = mean := by
    have boundaryIntegral : (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        positiveRepresentative value (children leaf)
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
        ∫ marks, positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable boundaryMeasurable
        (representativeMeasurable.comp (measurable_pi_apply leaf)).stronglyMeasurable
    rw [boundaryIntegral]
    have shiftIntegral : (∫ marks, positiveRepresentative value marks
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (innovationTreeShift rule (generationEdgeAddress rule depth leaf))) =
        ∫ marks, positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable
        (innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf)) representativeMeasurable.stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).map_eq] at shiftIntegral
    exact shiftIntegral.symm.trans ((integral_congr_ae representativeEquality).trans meanEquality)
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)
  have conditional := independent_conditional_electrical_mean_upper
    (independentInnovationLaw rule p positive belowOne fixedPoint) _ _ historyMeasurable boundaryMeasurable independent
    (rule.generation depth).network
    (fun data => markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) data) depth [] true)
    ((markedGenerationConfiguration_measurable rule depth [] true).comp (innovationPrefixFill_measurable rule (depth+1)))
    _ inputMeasurable (fun children leaf => positiveRepresentative_positive value (children leaf))
    inputIntegrable mean meanNonnegative inputMean
  rw [coordinatePrefixFiltration_eq_comap]
  simpa only [markedGenerationConfiguration_prefix_factor] using conditional


end
end IGSIII34.Percolation

