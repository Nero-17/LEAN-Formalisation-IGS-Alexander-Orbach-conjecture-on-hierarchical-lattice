import IGSIII34.Percolation.NormalizedOrbit
import IGSIII.Probability.IndependentTreeChildren

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped NNReal ENNReal

theorem connectedConfigurationLaw_eq_root (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    (connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure (Configuration rule.edges)) =
      Rule.ConfigurationHistory.law rule parameter positive belowOne fixedPoint true 0 := rfl

theorem innovationTree_value_joint_law (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (valueMeasurable : Measurable value) (law : ProbabilityMeasure ℝ≥0)
    (valueLaw : (independentInnovationLaw rule parameter positive belowOne fixedPoint).map value =
      (law : Measure ℝ≥0)) :
    (independentInnovationLaw rule parameter positive belowOne fixedPoint).map
        (fun marks => (marks ([], true), fun edge => value (innovationTreeShift rule [edge] marks))) =
      (electricalInputLaw rule parameter positive belowOne fixedPoint law :
        Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))) := by
  have joint := innovationTreeRoot_children_map rule parameter positive belowOne fixedPoint true
  rw [Measure.infinitePi_eq_pi] at joint
  have childMeasurable : Measurable (fun children : Fin rule.edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => fun edge => value (children edge)) :=
    measurable_pi_lambda _ (fun edge => valueMeasurable.comp (measurable_pi_apply edge))
  have transported := congrArg (fun measure => measure.map (Prod.map id
    (fun children : Fin rule.edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges) =>
      fun edge => value (children edge)))) joint
  rw [Measure.map_map (measurable_id.prodMap childMeasurable)
    ((measurable_pi_apply ([], true)).prodMk
      (measurable_pi_lambda _ (fun edge => innovationTreeShift_measurable rule [edge])))] at transported
  rw [← Measure.map_prod_map _ _ measurable_id childMeasurable, Measure.map_id,
    Measure.pi_map_pi (fun _ => valueMeasurable.aemeasurable)] at transported
  simp_rw [valueLaw] at transported
  change _ = (connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure (Configuration rule.edges)).prod
    (Measure.pi (fun _ : Fin rule.edges => (law : Measure ℝ≥0)))
  rw [connectedConfigurationLaw_eq_root]
  exact transported

theorem innovationTree_electrical_law (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (valueMeasurable : Measurable value) (law : ProbabilityMeasure ℝ≥0)
    (valueLaw : (independentInnovationLaw rule parameter positive belowOne fixedPoint).map value =
      (law : Measure ℝ≥0)) :
    (independentInnovationLaw rule parameter positive belowOne fixedPoint).map
      (fun marks => electricalCellNNReal rule.network (marks ([], true))
        (fun edge => value (innovationTreeShift rule [edge] marks))) =
      (electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0) := by
  have joint := innovationTree_value_joint_law rule parameter positive belowOne fixedPoint
    value valueMeasurable law valueLaw
  change _ = ((electricalInputLaw rule parameter positive belowOne fixedPoint law :
    Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
    (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) => electricalCellNNReal rule.network data.1 data.2))
  rw [← joint]
  exact (Measure.map_map
    (g := fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
      electricalCellNNReal rule.network data.1 data.2)
    (f := fun marks => (marks ([], true), fun edge => value (innovationTreeShift rule [edge] marks)))
    (electricalCellNNReal_joint_continuous rule.network).measurable
    ((measurable_pi_apply ([], true)).prodMk
      (measurable_pi_lambda _ (fun edge => valueMeasurable.comp (innovationTreeShift_measurable rule [edge]))))).symm

end
end IGSIII34.Percolation
