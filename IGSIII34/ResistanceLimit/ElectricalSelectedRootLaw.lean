import IGSIII34.ResistanceLimit.ElectricalComponentRootLaw
import IGSIII.Chemical.SubstitutionPaths.WeightedLeafLaw

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory ProbabilityTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))

/-- The full form-determining trace code has the root law even jointly with
the actual coarse selecting configuration. -/
theorem electrical_selected_trace_root_product_law
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => (markedGenerationConfiguration rule marks coarse [] true,
        electricalTraceCode rule p positive belowOne fixedPoint growth value
          (innovationTreeShift rule (generationEdgeAddress rule coarse chosen) marks))) =
    ((independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => markedGenerationConfiguration rule marks coarse [] true)).prod
    ((independentInnovationLaw rule p positive belowOne fixedPoint).map
      (electricalTraceCode rule p positive belowOne fixedPoint growth value)) := by
  have independent := (markedGeneration_leafTrees_independent rule p positive belowOne fixedPoint coarse).comp
    measurable_id ((electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value).comp
      (measurable_pi_apply chosen))
  simp only [Function.comp_def, id_eq] at independent
  have law := independent.map_prod_eq_prod_map_map
    (markedGenerationConfiguration_measurable rule coarse [] true).aemeasurable
    ((electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value).comp
      (innovationTreeShift_measurable rule (generationEdgeAddress rule coarse chosen))).aemeasurable
  simp only [Function.comp_def] at law
  rw [law, electricalTraceCode_descendant_law rule p positive belowOne fixedPoint growth value
      (generationEdgeAddress rule coarse chosen)]

/-- The entire actual coarse configuration, including the retained anchor
and the connected/noncrossing selecting bit, is independent of this local
completed energy. Both noncrossing side laws come from the same tree. -/
theorem electrical_selected_energy_independent
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    IndepFun (fun marks => markedGenerationConfiguration rule marks coarse [] true)
      (fun marks => electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value
          (innovationTreeShift rule (generationEdgeAddress rule coarse chosen) marks)) opened sourceSide potentials)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have independent := (markedGeneration_leafTrees_independent rule p positive belowOne fixedPoint coarse).comp
    measurable_id (((electricalTraceCodeLimitingEnergy_measurable rule opened sourceSide potentials).comp
      (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value)).comp (measurable_pi_apply chosen))
  simpa only [Function.comp_def, id_eq] using independent

/-- Exact joint law with the selecting configuration gives the root law
conditional on the actual connected socket and on its retained anchor. -/
theorem electrical_selected_energy_root_product_law
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) (opened sourceSide : Bool)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => (markedGenerationConfiguration rule marks coarse [] true,
        electricalTraceCodeLimitingEnergy rule
          (electricalTraceCode rule p positive belowOne fixedPoint growth value
            (innovationTreeShift rule (generationEdgeAddress rule coarse chosen) marks)) opened sourceSide potentials)) =
    ((independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => markedGenerationConfiguration rule marks coarse [] true)).prod
    ((independentInnovationLaw rule p positive belowOne fixedPoint).map
      (fun marks => electricalTraceCodeLimitingEnergy rule
        (electricalTraceCode rule p positive belowOne fixedPoint growth value marks) opened sourceSide potentials)) := by
  have law := (electrical_selected_energy_independent rule p positive belowOne fixedPoint growth value coarse chosen
    opened sourceSide potentials).map_prod_eq_prod_map_map
      (markedGenerationConfiguration_measurable rule coarse [] true).aemeasurable
      (((electricalTraceCodeLimitingEnergy_measurable rule opened sourceSide potentials).comp
        (electricalTraceCode_measurable rule p positive belowOne fixedPoint growth value)).comp
        (innovationTreeShift_measurable rule (generationEdgeAddress rule coarse chosen))).aemeasurable
  simp only [Function.comp_def] at law
  rw [law, electrical_limiting_energy_descendant_law rule p positive belowOne fixedPoint growth value
      (generationEdgeAddress rule coarse chosen) opened sourceSide potentials]

end
end IGSIII34.ResistanceLimit
