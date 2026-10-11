import IGSIII34.Percolation.Continuation.ElectricalBoundaryWeighted
import IGSIII34.Percolation.ElectricalPrefix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

private def electricalBoundaryPrefixIndex (rule : Rule) (depth : ℕ) : Bool → Type
  | false => {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}
  | true => Fin (rule.generation depth).edges

private def electricalBoundaryPrefixCoordinate (rule : Rule) (depth : ℕ) :
    ((group : Bool) × electricalBoundaryPrefixIndex rule depth group) → List (Fin rule.edges) × Bool
  | ⟨false, coordinate⟩ => coordinate.val
  | ⟨true, leaf⟩ => (generationEdgeAddress rule depth leaf, true)

private theorem electricalBoundaryPrefixCoordinate_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (electricalBoundaryPrefixCoordinate rule depth) := by
  rintro ⟨firstGroup, first⟩ ⟨secondGroup, second⟩ equality
  cases firstGroup <;> cases secondGroup
  · have same : first.val = second.val := equality
    cases Subtype.ext same
    rfl
  · change first.val = (generationEdgeAddress rule depth second, true) at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    rw [generationEdgeAddress_length] at lengths
    have short := first.property
    omega
  · change (generationEdgeAddress rule depth first, true) = second.val at equality
    have lengths := congrArg (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) equality
    rw [generationEdgeAddress_length] at lengths
    have short := second.property
    omega
  · have same := generationEdgeAddress_injective rule depth (congrArg Prod.fst equality)
    cases same
    rfl

theorem electricalBoundaryTree_configuration_frontier_independent (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    IndepFun
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
      (fun sample leaf => (sample (generationEdgeAddress rule depth leaf, true)).2)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  have independent := infinitePi_subfamilies_independent
    (fun coordinate : List (Fin rule.edges) × Bool =>
      (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0).prod (law : Measure ℝ≥0))
    (electricalBoundaryPrefixCoordinate rule depth) (electricalBoundaryPrefixCoordinate_injective rule depth)
  have two := independent.indepFun (i := false) (j := true) Bool.false_ne_true
  have configurationMeasurable : Measurable (fun history :
      {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges × ℝ≥0 =>
      markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) (fun coordinate => (history coordinate).1)) depth [] true) :=
    (markedGenerationConfiguration_measurable rule depth [] true).comp
      ((innovationPrefixFill_measurable rule (depth+1)).comp
        (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate))))
  have transported := two.comp configurationMeasurable
    (measurable_pi_lambda _ (fun leaf => measurable_snd.comp (measurable_pi_apply leaf)))
  dsimp only [Function.comp_def, electricalBoundaryPrefixCoordinate] at transported
  have prefixEquality (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :=
    markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) depth true
  simp_rw [prefixEquality] at transported
  exact transported

theorem electricalBoundaryTree_configuration_preserving (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    MeasurePreserving
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth [] true)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
      ((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true)) := by
  refine ⟨(markedGenerationConfiguration_measurable rule depth [] true).comp
    (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate))), ?_⟩
  rw [← electricalBoundaryInnovationLaw_marks_map rule p positive belowOne fixedPoint law,
    Measure.map_map (f := fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate => (sample coordinate).1) (markedGenerationConfiguration_measurable rule depth [] true)
      (measurable_pi_lambda _ (fun coordinate => measurable_fst.comp (measurable_pi_apply coordinate)))]
  rfl

end
end IGSIII34.Percolation
