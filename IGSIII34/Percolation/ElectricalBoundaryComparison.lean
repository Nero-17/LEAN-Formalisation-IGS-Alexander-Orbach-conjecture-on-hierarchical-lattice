import IGSIII34.Percolation.ElectricalFrontierMarginals
import IGSIII34.Percolation.ElectricalConditionalComparison
import IGSIII34.Probability.PrefixMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

theorem actual_electrical_boundary_conditional_pair_comparison (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (firstPositive : ∀ marks, 0 < first marks) (secondPositive : ∀ marks, 0 < second marks)
    (firstIntegrable : Integrable first (independentInnovationLaw rule p positive belowOne fixedPoint))
    (secondIntegrable : Integrable second (independentInnovationLaw rule p positive belowOne fixedPoint))
    (numeratorIntegrable : Integrable (fun marks => max (first marks-second marks) 0 * max 1 ((second marks)⁻¹^2))
      (independentInnovationLaw rule p positive belowOne fixedPoint))
    {numerator denominator : ℝ} (numeratorNonnegative : 0 ≤ numerator) (denominatorPositive : 0 < denominator)
    (numeratorEquality : (∫ marks, max (first marks-second marks) 0 * max 1 ((second marks)⁻¹^2)
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = numerator)
    (denominatorEquality : (∫ marks, min (second marks) (second marks)⁻¹
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = denominator)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks => max
        (electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => first (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))-
        electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => second (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))) 0 |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
      (numerator/denominator) * (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks =>
        electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => second (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
  have historyMeasurable : Measurable (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
      (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}) => marks coordinate.val) :=
    measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)
  have boundaryMeasurable := generationFrontier_measurable rule depth
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)
  have conditional := independent_conditional_electrical_pair_comparison
    (independentInnovationLaw rule p positive belowOne fixedPoint) _ _ historyMeasurable boundaryMeasurable independent
    (rule.generation depth).network
    (fun data => markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) data) depth [] true)
    ((markedGenerationConfiguration_measurable rule depth [] true).comp (innovationPrefixFill_measurable rule (depth+1)))
    (fun leaf children => children leaf) (generationFrontier_eval_independent rule p positive belowOne fixedPoint depth)
    (fun leaf => measurable_pi_apply leaf) (fun _ _ => false)
    first second firstMeasurable secondMeasurable firstPositive secondPositive
    (fun leaf => (generationFrontier_eval_preserving rule p positive belowOne fixedPoint depth leaf).integrable_comp_of_integrable firstIntegrable)
    (fun leaf => (generationFrontier_eval_preserving rule p positive belowOne fixedPoint depth leaf).integrable_comp_of_integrable secondIntegrable)
    (fun leaf => (generationFrontier_eval_preserving rule p positive belowOne fixedPoint depth leaf).integrable_comp_of_integrable numeratorIntegrable)
    numeratorNonnegative denominatorPositive
    (fun leaf => (generationFrontier_eval_integral rule p positive belowOne fixedPoint depth leaf _
      (((firstMeasurable.sub secondMeasurable).max measurable_const).mul
        (measurable_const.max (secondMeasurable.inv.pow_const 2))).stronglyMeasurable).trans numeratorEquality)
    (fun leaf => (generationFrontier_eval_integral rule p positive belowOne fixedPoint depth leaf _
      (secondMeasurable.min secondMeasurable.inv).stronglyMeasurable).trans denominatorEquality)
  rw [coordinatePrefixFiltration_eq_comap]
  simpa only [markedGenerationConfiguration_prefix_factor] using conditional

end
end IGSIII34.Percolation

