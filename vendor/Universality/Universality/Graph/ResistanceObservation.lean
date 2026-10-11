import Universality.Graph.ConductanceMultiplicativity
import Universality.Graph.ConnectedConductance
import Universality.Examples.PhysicalClassCounterexample

namespace Universality.Rule
noncomputable section

/-- Scalar resistance observation; the physical interpretation is used on connected rules. -/
def effectiveResistance (rule : Rule) : ℝ := rule.network.unitConductance⁻¹

theorem effectiveResistance_mul (outer inner : Rule) :
    (outer * inner).effectiveResistance = outer.effectiveResistance * inner.effectiveResistance := by
  change (outer.network.substitute inner.network).unitConductance⁻¹ =
    outer.network.unitConductance⁻¹ * inner.network.unitConductance⁻¹
  rw [FiniteNetwork.substitute_unitConductance, mul_inv_rev,
    mul_comm inner.network.unitConductance⁻¹ outer.network.unitConductance⁻¹]

theorem Classical.effectiveResistance_pos {rule : Rule} (h : rule.Classical) :
    0 < rule.effectiveResistance :=
  inv_pos.mpr (rule.network.unitConductance_pos_of_connected (h.connected rule.network.target))

end
end Universality.Rule

namespace Universality
noncomputable section
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem equal_resistance_dimension_does_not_classify :
    Real.log groupedRule.effectiveResistance /
      Real.log (groupedRule.network.fullGraph.dist groupedRule.network.source groupedRule.network.target) =
    Real.log alternatingRule.effectiveResistance /
      Real.log (alternatingRule.network.fullGraph.dist alternatingRule.network.source alternatingRule.network.target) ∧
    ¬ Rule.SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) := by
  obtain ⟨heq, hne⟩ := multiplicative_dimensions_fail_physical_classification
    (fun (_ : Unit) rule => rule.effectiveResistance)
    (fun _ outer inner _ _ _ => Rule.effectiveResistance_mul outer inner)
  exact ⟨congrFun heq (), hne⟩

end
end Universality
