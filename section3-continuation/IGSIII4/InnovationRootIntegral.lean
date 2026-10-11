import IGSIII.Chemical.SubstitutionPaths.IndependentInnovations
import Universality.Percolation.InfiniteObservables

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution

theorem innovation_root_integral (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (observable : Configuration rule.edges → ℝ) :
    (∫ marks, observable (marks ([], true))
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
      ∑ configuration, rule.network.conditionalCellWeight probability true configuration * observable configuration := by
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply ([], true))
    (measurable_of_finite observable).stronglyMeasurable,
    independentInnovationLaw_marginal, Rule.ConfigurationHistory.integral_law]
  rfl

end
end IGSIII4
