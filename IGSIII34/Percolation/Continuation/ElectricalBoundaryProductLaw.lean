import IGSIII34.Percolation.Continuation.ElectricalBoundaryIndependence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped NNReal ENNReal

theorem electricalBoundaryTree_frontier_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample (leaf : Fin (rule.generation depth).edges) =>
        (sample (generationEdgeAddress rule depth leaf, true)).2) =
      Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  letI : IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint true 0) :=
    Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint true 0
  have injective : Function.Injective (fun leaf : Fin (rule.generation depth).edges =>
      (generationEdgeAddress rule depth leaf, true)) := by
    intro first second equality
    exact generationEdgeAddress_injective rule depth (congrArg Prod.fst equality)
  have flat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law:Measure ℝ≥0)) injective
  change (Measure.infinitePi _).map
    ((fun input : Fin (rule.generation depth).edges → Configuration rule.edges × ℝ≥0 => fun leaf => (input leaf).2) ∘
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        fun leaf : Fin (rule.generation depth).edges => sample (generationEdgeAddress rule depth leaf, true))) = _
  rw [← Measure.map_map (g := fun input : Fin (rule.generation depth).edges → Configuration rule.edges × ℝ≥0 =>
      fun leaf => (input leaf).2)
    (f := fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun leaf : Fin (rule.generation depth).edges => sample (generationEdgeAddress rule depth leaf, true))
    (by fun_prop) (by fun_prop), flat, Measure.infinitePi_map_pi _ (fun _ => measurable_snd)]
  simp only [Measure.map_snd_prod]
  simp only [measure_univ, one_smul, Measure.infinitePi_eq_pi]

theorem electricalBoundaryTree_configuration_frontier_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample => (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true,
        fun leaf : Fin (rule.generation depth).edges => (sample (generationEdgeAddress rule depth leaf, true)).2)) =
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true)).prod
        (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))) := by
  have independent := electricalBoundaryTree_configuration_frontier_independent rule p positive belowOne fixedPoint law depth
  have joint := independent.map_prod_eq_prod_map_map
      ((markedGenerationConfiguration_measurable rule depth [] true).comp
        (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))).aemeasurable
      (measurable_pi_lambda _ (fun leaf => measurable_snd.comp
        (measurable_pi_apply (generationEdgeAddress rule depth leaf, true)))).aemeasurable
  dsimp only [Function.comp_def] at joint
  rw [joint, electricalBoundaryTree_frontier_map,
    (electricalBoundaryTree_configuration_preserving rule p positive belowOne fixedPoint law depth).map_eq]

end
end IGSIII34.Percolation
