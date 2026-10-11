import IGSIII4.InnovationFiltration
import IGSIII.Chemical.SubstitutionPaths.WeightedGeneration

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability

theorem generationFrontier_independent_filtration (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    {Input : Type*} [MeasurableSpace Input]
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Input)
    (measurable : Measurable value) (depth : ℕ) :
    Indep (MeasurableSpace.comap
      (fun marks edge => value (innovationTreeShift rule (generationEdgeAddress rule depth edge) marks))
      (inferInstance : MeasurableSpace (Fin (rule.generation depth).edges → Input)))
      (innovationFiltration rule (depth + 1))
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
  have independent := innovationPrefix_frontier_independent rule probability positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth)
    (depth + 1) (generationEdgeAddress_length rule depth)
  have valuesIndependent := independent.comp measurable_id
    (measurable_pi_lambda _ (fun edge => measurable.comp (measurable_pi_apply edge)))
  rw [innovationFiltration_eq_prefix]
  exact valuesIndependent.symm

end
end IGSIII4
