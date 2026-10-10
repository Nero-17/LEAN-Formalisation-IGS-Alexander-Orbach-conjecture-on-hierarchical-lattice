import IGSIII.Geometry.ActualChemicalSkeleton

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution Filter
open scoped Topology

theorem weightedDistance_scale {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ) (factor : ℝ) (factorNonnegative : 0 ≤ factor)
    (first last : Vertex) :
    weightedDistance graph (fun bond => factor * cost bond) first last = factor * weightedDistance graph cost first last := by
  by_cases reachable : graph.Reachable first last
  · rw [weightedDistance_of_reachable graph _ reachable, weightedDistance_of_reachable graph _ reachable]
    exact (graphPathFamily graph first last reachable).shortest_scale cost factorNonnegative
  · simp only [weightedDistance, dif_neg reachable, mul_zero]

theorem indexedBondCost_scale {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (values : Fin edges → ℝ) (factor : ℝ) :
    indexedBondCost network (fun edge => factor * values edge) = fun bond => factor * indexedBondCost network values bond := by
  funext bond
  unfold indexedBondCost
  split_ifs <;> simp only [mul_zero]

/-- Intrinsic component skeletons are measured in root units. The extra
generation offset multiplies all local limiting lengths by the same factor,
and does not alter their proved compatibility. -/
theorem actual_skeleton_weighted_distance_compatible_offset (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale) (offset : ℕ)
    (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge)))
    (depth : ℕ) {first last : Fin (rule.generation depth).vertices}
    (reachable : ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last) :
    weightedDistance ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1)))
      (indexedBondCost (rule.generation (depth + 1)).network (values (depth + 1)))
      (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
      (indexedBondCost (rule.generation depth).network (values depth)) first last := by
  have scaledConvergence (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
      Tendsto (fun fine =>
        (((rule.generation fine).network.openGraph
          (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
            (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
          scale ^ (coarse + fine + 2)) atTop (𝓝 (scale ^ offset * values coarse edge)) := by
    convert (childConvergence coarse edge).const_mul (scale ^ offset) using 1
    funext fine
    simp only [pow_add]
    field_simp
  have compatibility := actual_skeleton_weighted_distance_compatible rule classicalRule configuration coherent scale scalePositive
    (fun coarse edge => scale ^ offset * values coarse edge) scaledConvergence depth reachable
  simp only [indexedBondCost_scale, weightedDistance_scale _ _ _ (pow_pos scalePositive offset).le] at compatibility
  exact mul_left_cancel₀ (pow_pos scalePositive offset).ne' compatibility

theorem actual_persistent_skeleton_distances_tendsto_offset (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale) (offset coarse : ℕ)
    (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge)))
    {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable first last) :
    Tendsto (fun host => persistentNormalizedDistance rule configuration scale coarse first last host / scale ^ offset)
      atTop (𝓝 (weightedDistance ((rule.generation coarse).network.openGraph (configuration coarse))
        (indexedBondCost (rule.generation coarse).network (values coarse)) first last)) := by
  have scaledConvergence (depth : ℕ) (edge : Fin (rule.generation depth).edges) :
      Tendsto (fun fine =>
        (((rule.generation fine).network.openGraph
          (generationBlockCells rule depth fine (configuration (depth + fine + 1)) edge)).dist
            (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
          scale ^ (depth + fine + 2)) atTop (𝓝 (scale ^ offset * values depth edge)) := by
    convert (childConvergence depth edge).const_mul (scale ^ offset) using 1
    funext fine
    simp only [pow_add]
    field_simp
  have convergence := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive coarse
    (fun edge => scale ^ offset * values coarse edge) (scaledConvergence coarse) reachable).div_const (scale ^ offset)
  simpa only [indexedBondCost_scale, weightedDistance_scale _ _ _ (pow_pos scalePositive offset).le,
    mul_div_cancel_left₀ _ (pow_pos scalePositive offset).ne'] using convergence

end
end IGSIII.Geometry
