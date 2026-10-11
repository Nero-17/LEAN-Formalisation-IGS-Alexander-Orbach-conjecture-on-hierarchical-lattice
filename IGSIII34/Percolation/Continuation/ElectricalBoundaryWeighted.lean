import IGSIII34.Percolation.Continuation.ElectricalBoundaryTree
import IGSIII34.Percolation.ElectricalWeightedGeneration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

theorem electricalBoundaryTreeShift_append (rule : Rule)
    (first second : List (Fin rule.edges))
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :
    electricalBoundaryTreeShift rule second (electricalBoundaryTreeShift rule first sample) =
      electricalBoundaryTreeShift rule (first++second) sample := by
  funext coordinate
  simp only [electricalBoundaryTreeShift, List.append_assoc]

theorem electricalBoundaryTreeIteration_weighted_actual (rule : Rule)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0)
    (crossing : ∀ address opened, rule.network.crosses (sample (address, opened)).1 = opened)
    (positive : ∀ address, 0 < (sample (address, true)).2)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (electricalBoundaryTreeIteration rule (depth+1) (electricalBoundaryTreeShift rule address sample) : ℝ) =
      electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule (fun coordinate => (sample coordinate).1) depth address true)
        (fun leaf => ((sample (address++generationEdgeAddress rule depth leaf, true)).2 : ℝ)) := by
  induction depth generalizing address with
  | zero =>
      change electricalCell rule.network (sample (address++[], true)).1
        (fun edge => ((sample (address++([edge]++[]), true)).2 : ℝ)) = _
      simp only [List.append_nil, generationEdgeAddress, Rule.generation, markedGenerationConfiguration]
  | succ depth inductionHypothesis =>
      change electricalCell rule.network (sample (address++[], true)).1
        (fun edge => (electricalBoundaryTreeIteration rule (depth+1)
          (electricalBoundaryTreeShift rule [edge] (electricalBoundaryTreeShift rule address sample)) : ℝ)) = _
      rw [generation_weighted_resistance_recursion rule depth _
        (markedGenerationConfiguration_crosses rule _ crossing (depth+1) address true)
        _ (fun leaf => by exact_mod_cast positive (address++generationEdgeAddress rule (depth+1) leaf)),
        markedGenerationConfiguration_root rule _ crossing, markedGenerationConfiguration_topCells]
      simp only [List.append_nil]
      apply electricalCell_depends_open rule.network (sample (address, true)).1
      intro edge retained
      rw [retained, electricalBoundaryTreeShift_append, inductionHypothesis]
      congr 1
      funext child
      rw [generationEdgeAddress_top]
      simp only [List.append_assoc, List.singleton_append]

theorem electricalBoundaryInnovationLaw_marks_map (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law).map
      (fun sample coordinate => (sample coordinate).1) = independentInnovationLaw rule p positive belowOne fixedPoint := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  unfold electricalBoundaryInnovationLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
  simp only [Measure.map_fst_prod, measure_univ, one_smul]
  rfl

theorem electricalBoundaryInnovationLaw_boundary_preserving (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (law : ProbabilityMeasure ℝ≥0)
    (address : List (Fin rule.edges)) :
    MeasurePreserving (fun sample => (sample (address, true)).2)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) (law : Measure ℝ≥0) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  refine ⟨measurable_snd.comp (measurable_pi_apply (address, true)), ?_⟩
  change (Measure.infinitePi _).map (Prod.snd ∘ fun sample :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 => sample (address, true)) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply (address, true)), Measure.infinitePi_map_eval,
    Measure.map_snd_prod, measure_univ, one_smul]

end
end IGSIII34.Percolation
