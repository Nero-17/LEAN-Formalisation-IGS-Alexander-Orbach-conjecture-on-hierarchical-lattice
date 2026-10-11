import IGSIII34.Percolation.LawMap
import IGSIII.Probability.IndependentTreeChildren

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation
open scoped NNReal ENNReal

def innovationValueLaw (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) : ProbabilityMeasure ℝ≥0 :=
  ⟨(independentInnovationLaw rule probability positive belowOne fixedPoint).map value,
    Measure.isProbabilityMeasure_map measurable.aemeasurable⟩

def electricalTransferNNReal (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ≥0 :=
  electricalCellNNReal rule.network (marks ([], true))
    (fun edge => value (innovationTreeShift rule [edge] marks))

theorem electricalTransferNNReal_measurable (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) : Measurable (electricalTransferNNReal rule value) := by
  exact (electricalCellNNReal_joint_continuous rule.network).measurable.comp
    ((measurable_pi_apply ([], true)).prodMk
      (measurable_pi_lambda _ fun edge => measurable.comp (innovationTreeShift_measurable rule [edge])))

theorem electricalTransferNNReal_law (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) :
    (independentInnovationLaw rule probability positive belowOne fixedPoint).map
      (electricalTransferNNReal rule value) =
        (electricalOutputLaw rule probability positive belowOne fixedPoint
          (innovationValueLaw rule probability positive belowOne fixedPoint value measurable) : Measure ℝ≥0) := by
  have childMeasurable (edge : Fin rule.edges) :
      Measurable (fun marks => value (innovationTreeShift rule [edge] marks)) :=
    measurable.comp (innovationTreeShift_measurable rule [edge])
  have childLaw (edge : Fin rule.edges) :
      (independentInnovationLaw rule probability positive belowOne fixedPoint).map
        (fun marks => value (innovationTreeShift rule [edge] marks)) =
      (innovationValueLaw rule probability positive belowOne fixedPoint value measurable : Measure ℝ≥0) := by
    change (independentInnovationLaw rule probability positive belowOne fixedPoint).map
      (value ∘ innovationTreeShift rule [edge]) = _
    rw [← Measure.map_map measurable (innovationTreeShift_measurable rule [edge]),
      (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).map_eq]
    rfl
  have childIndependent := (innovationTreeChildren_independent rule probability positive belowOne fixedPoint).comp
    (fun _ => value) (fun _ => measurable)
  have childrenLaw := childIndependent.map_fun_eq_pi_map (fun edge => (childMeasurable edge).aemeasurable)
  simp only [Function.comp_def, childLaw] at childrenLaw
  have rootIndependent := (innovationTreeRoot_children_independent rule probability positive belowOne fixedPoint true).comp
    measurable_id (measurable_pi_lambda _ fun edge => measurable.comp (measurable_pi_apply edge))
  have jointLaw := rootIndependent.map_prod_eq_prod_map_map
    (measurable_pi_apply ([], true)).aemeasurable
    (measurable_pi_lambda _ fun edge => childMeasurable edge).aemeasurable
  rw [independentInnovationLaw_marginal, childrenLaw] at jointLaw
  have rootLaw : Rule.ConfigurationHistory.law rule probability positive belowOne fixedPoint true 0 =
      (connectedConfigurationLaw rule probability positive belowOne fixedPoint : Measure _) := rfl
  rw [rootLaw] at jointLaw
  change _ = (((connectedConfigurationLaw rule probability positive belowOne fixedPoint :
      Measure (Configuration rule.edges)).prod
        (Measure.pi (fun _ : Fin rule.edges =>
          (innovationValueLaw rule probability positive belowOne fixedPoint value measurable : Measure ℝ≥0)))).map
      (fun data => electricalCellNNReal rule.network data.1 data.2))
  rw [← jointLaw, Measure.map_map (electricalCellNNReal_joint_continuous rule.network).measurable
    ((measurable_pi_apply ([], true)).prodMk (measurable_pi_lambda _ childMeasurable))]
  rfl

end
end IGSIII4
