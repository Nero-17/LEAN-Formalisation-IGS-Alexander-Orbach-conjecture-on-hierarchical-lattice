import IGSIII34.Percolation.ElectricalWeightedGeneration
import IGSIII.Probability.IndependentPrefix
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution

def innovationPrefixFill (rule : Rule) (depth : ℕ)
    (input : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} → Configuration rule.edges) :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges :=
  fun coordinate => if within : coordinate.1.length < depth then input ⟨coordinate, within⟩ else fun _ => false

theorem innovationPrefixFill_measurable (rule : Rule) (depth : ℕ) : Measurable (innovationPrefixFill rule depth) := by
  apply measurable_pi_lambda
  intro coordinate
  by_cases within : coordinate.1.length < depth
  · simpa only [innovationPrefixFill, dif_pos within] using (measurable_pi_apply (⟨coordinate, within⟩ : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}))
  · simpa only [innovationPrefixFill, dif_neg within] using
      (measurable_const : Measurable (fun _ : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} → Configuration rule.edges => (fun _ : Fin rule.edges => false)))

theorem markedGenerationConfiguration_congr_prefix (rule : Rule)
    (first second : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (agree : ∀ suffix : List (Fin rule.edges), ∀ state : Bool, suffix.length ≤ depth →
      first (address ++ suffix, state) = second (address ++ suffix, state)) :
    markedGenerationConfiguration rule first depth address opened = markedGenerationConfiguration rule second depth address opened := by
  induction depth generalizing address opened with
  | zero =>
      simpa only [markedGenerationConfiguration, List.append_nil] using agree [] opened (by simp)
  | succ depth inductionHypothesis =>
      have rootEquality : first (address, opened) = second (address, opened) := by
        simpa only [List.append_nil] using agree [] opened (by simp)
      simp only [markedGenerationConfiguration, rootEquality]
      congr 2
      funext edge
      apply inductionHypothesis
      intro suffix state length
      have equality := agree ([edge] ++ suffix) state (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.append_assoc] using equality

theorem markedGenerationConfiguration_prefix_factor (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ) (opened : Bool) :
    markedGenerationConfiguration rule
      (innovationPrefixFill rule (depth+1) (fun coordinate => marks coordinate.val)) depth [] opened =
      markedGenerationConfiguration rule marks depth [] opened := by
  apply markedGenerationConfiguration_congr_prefix
  intro suffix state length
  simp only [List.nil_append, innovationPrefixFill, dif_pos (show suffix.length < depth+1 from Nat.lt_succ_of_le length)]

theorem markedGenerationConfiguration_frontier_independent (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (opened : Bool) :
    IndepFun (fun marks => markedGenerationConfiguration rule marks depth [] opened)
      (fun marks (edge : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth edge) marks)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)
  have transported := independent.comp
    ((markedGenerationConfiguration_measurable rule depth [] opened).comp (innovationPrefixFill_measurable rule (depth+1))) measurable_id
  simpa only [Function.comp_def, markedGenerationConfiguration_prefix_factor, id_eq] using transported

end
end IGSIII34.Percolation
