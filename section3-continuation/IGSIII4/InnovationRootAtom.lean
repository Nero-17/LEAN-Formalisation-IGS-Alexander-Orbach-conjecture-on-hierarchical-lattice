import IGSIII.Chemical.SubstitutionPaths.IndependentInnovations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution

theorem innovation_root_atom_positive (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (configuration : Configuration rule.edges) (crossing : rule.network.crosses configuration = true) :
    0 < (independentInnovationLaw rule probability positive belowOne fixedPoint)
      {marks | marks ([], true) = configuration} := by
  have weightPositive : 0 < rule.network.conditionalCellWeight probability true configuration := by
    simp only [conditionalCellWeight, crossing, if_pos rfl, Bool.true_eq, ite_true, fixedPoint]
    exact div_pos (bernoulliWeight_pos positive belowOne configuration) positive
  have marginal := congrArg (fun measure => measure {configuration})
    (independentInnovationLaw_marginal rule probability positive belowOne fixedPoint [] true)
  rw [Measure.map_apply (measurable_pi_apply ([], true)) (measurableSet_singleton configuration)] at marginal
  have atomIdentity : (independentInnovationLaw rule probability positive belowOne fixedPoint)
      {marks | marks ([], true) = configuration} = ENNReal.ofReal
        (rule.network.conditionalCellWeight probability true configuration) := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Rule.ConfigurationHistory.law, finiteWeightPMF_singleton,
      Rule.ConfigurationHistory.recursiveWeight] using marginal
  rw [atomIdentity]
  exact ENNReal.ofReal_pos.mpr weightPositive

end
end IGSIII4
