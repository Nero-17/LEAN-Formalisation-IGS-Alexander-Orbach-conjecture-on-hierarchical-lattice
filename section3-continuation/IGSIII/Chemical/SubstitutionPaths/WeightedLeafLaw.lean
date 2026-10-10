import IGSIII.Chemical.SubstitutionPaths.WeightedGeneration
import IGSIII.Probability.IndependentPrefix
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability

theorem generationLeafTrees_map (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
      (fun marks leaf => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) =
        Measure.infinitePi (fun _ : Fin (rule.generation depth).edges =>
          independentInnovationLaw rule p positive lessOne fixedPoint) :=
  innovationFrontier_map rule p positive lessOne fixedPoint (generationEdgeAddress rule depth)
    (generationEdgeAddress_injective rule depth) (depth + 1) (generationEdgeAddress_length rule depth)

theorem generationLeafTrees_independent (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    iIndepFun (fun leaf => innovationTreeShift rule (generationEdgeAddress rule depth leaf))
      (independentInnovationLaw rule p positive lessOne fixedPoint) :=
  innovationFrontier_independent rule p positive lessOne fixedPoint (generationEdgeAddress rule depth)
    (generationEdgeAddress_injective rule depth) (depth + 1) (generationEdgeAddress_length rule depth)

theorem markedGenerationConfiguration_congr_prefix (rule : Rule)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (first second : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (same : ∀ coordinate, coordinate.1.length ≤ address.length + depth → first coordinate = second coordinate) :
    markedGenerationConfiguration rule first depth address opened =
      markedGenerationConfiguration rule second depth address opened := by
  induction depth generalizing address opened with
  | zero => exact same (address, opened) (by change address.length ≤ address.length + 0; omega)
  | succ depth inductionHypothesis =>
      have root := same (address, opened) (by change address.length ≤ address.length + (depth + 1); omega)
      change (generationTopCellsEquiv rule depth).symm
          (fun edge => markedGenerationConfiguration rule first depth (address ++ [edge]) (first (address, opened) edge)) =
        (generationTopCellsEquiv rule depth).symm
          (fun edge => markedGenerationConfiguration rule second depth (address ++ [edge]) (second (address, opened) edge))
      rw [root]
      apply congrArg (generationTopCellsEquiv rule depth).symm
      funext edge
      apply inductionHypothesis
      intro coordinate short
      apply same
      simp only [List.length_append, List.length_singleton] at short
      omega

def innovationPrefixCompletion (rule : Rule) (depth : ℕ)
    (prefixValues : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} → Configuration rule.edges) :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges :=
  fun coordinate => if short : coordinate.1.length < depth then prefixValues ⟨coordinate, short⟩ else fun _ => false

theorem innovationPrefixCompletion_measurable (rule : Rule) (depth : ℕ) :
    Measurable (innovationPrefixCompletion rule depth) := by
  apply measurable_pi_lambda
  intro coordinate
  unfold innovationPrefixCompletion
  split
  · exact measurable_pi_apply _
  · exact measurable_const

noncomputable def generationConfigurationFromPrefix (rule : Rule) (depth : ℕ)
    (prefixValues : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth + 1} → Configuration rule.edges) :
    Configuration (rule.generation depth).edges :=
  markedGenerationConfiguration rule (innovationPrefixCompletion rule (depth + 1) prefixValues) depth [] true

theorem generationConfigurationFromPrefix_measurable (rule : Rule) (depth : ℕ) :
    Measurable (generationConfigurationFromPrefix rule depth) :=
  (markedGenerationConfiguration_measurable rule depth [] true).comp
    (innovationPrefixCompletion_measurable rule (depth + 1))

theorem markedGenerationConfiguration_fromPrefix (rule : Rule) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    generationConfigurationFromPrefix rule depth (fun coordinate => marks coordinate.val) =
      markedGenerationConfiguration rule marks depth [] true := by
  apply markedGenerationConfiguration_congr_prefix
  intro coordinate short
  have bound : coordinate.1.length < depth + 1 := by simpa only [List.length_nil, Nat.zero_add] using Nat.lt_succ_of_le short
  simp only [innovationPrefixCompletion, dif_pos bound]

theorem markedGeneration_leafTrees_independent (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    IndepFun (fun marks => markedGenerationConfiguration rule marks depth [] true)
      (fun marks leaf => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
  have independent := innovationPrefix_frontier_independent rule p positive lessOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth)
    (depth + 1) (generationEdgeAddress_length rule depth)
  have composition := independent.comp (generationConfigurationFromPrefix_measurable rule depth) measurable_id
  simpa only [Function.comp_def, id_eq, markedGenerationConfiguration_fromPrefix] using composition

theorem markedGeneration_leafTrees_map (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => (markedGenerationConfiguration rule marks depth [] true,
          fun leaf => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
      ((independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true)).prod
          (Measure.infinitePi (fun _ : Fin (rule.generation depth).edges =>
            independentInnovationLaw rule p positive lessOne fixedPoint)) := by
  rw [(markedGeneration_leafTrees_independent rule p positive lessOne fixedPoint depth).map_prod_eq_prod_map_map
    (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
    (measurable_pi_lambda _ (fun leaf => innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf))).aemeasurable,
    generationLeafTrees_map]

end IGSIII.Chemical.Substitution
