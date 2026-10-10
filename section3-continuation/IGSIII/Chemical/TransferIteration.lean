import IGSIII.Chemical.TransferOperator
import IGSIII.Chemical.SubstitutionPaths.BlockPaths
import IGSIII.Chemical.SubstitutionPaths.ConnectedProductLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability

theorem markedGenerationConfiguration_shift (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (addressPrefix address : List (Fin rule.edges)) (opened : Bool) (depth : ℕ) :
    markedGenerationConfiguration rule (innovationTreeShift rule addressPrefix marks) depth address opened =
      markedGenerationConfiguration rule marks depth (addressPrefix ++ address) opened := by
  induction depth generalizing address opened with
  | zero => rfl
  | succ depth inductionHypothesis =>
    simp only [markedGenerationConfiguration, innovationTreeShift]
    congr 1
    apply congrArg (substitutionConfigurationEquiv)
    funext edge
    simpa only [List.append_assoc] using inductionHypothesis (address ++ [edge]) (marks (addressPrefix ++ address, opened) edge)

theorem chemicalTransfer_iterate_eq_actual (rule : Rule)
    (simple : Function.Injective (fun edge => s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (chemicalTransfer rule)^[depth + 1] (fun _ => 1) (innovationTreeShift rule address marks) =
      (((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth address true)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) := by
  induction depth generalizing address with
  | zero =>
    change (edgePathFamily rule.network (marks (address ++ [], true))).shortest (fun _ => 1) = _
    simpa only [List.append_nil, Rule.generation, markedGenerationConfiguration] using
      edgePathFamily_shortest_unit rule.network simple (marks (address, true))
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', chemicalTransfer,
      generation_distance_eq_cellMinPlus rule simple,
      markedGenerationConfiguration_root rule marks crossing,
      cellMinPlus_eq_edgePathFamily_shortest rule.network (rule.generation depth).network simple,
      markedGenerationConfiguration_topCells]
    simp only [innovationTreeShift, List.append_nil]
    apply edgePathFamily_shortest_depends_open rule.network simple (marks (address, true))
    intro edge retained
    rw [retained]
    simpa only [innovationTreeShift_append] using inductionHypothesis (address ++ [edge])

theorem chemicalTransfer_iterate_eq_actual_ae (rule : Rule)
    (simple : Function.Injective (fun edge => s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ depth address,
        (chemicalTransfer rule)^[depth + 1] (fun _ => 1) (innovationTreeShift rule address marks) =
          (((rule.generation depth).network.openGraph
            (markedGenerationConfiguration rule marks depth address true)).dist
              (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) := by
  filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crossing
  exact fun depth address => chemicalTransfer_iterate_eq_actual rule simple marks crossing depth address

end IGSIII.Chemical.Substitution


