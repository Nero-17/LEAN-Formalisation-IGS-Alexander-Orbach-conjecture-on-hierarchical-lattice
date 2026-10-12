import IGSIII34.ResistanceLimit.GenerationAvailableAnchorsCompletion

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem generation_block_distinct_components_available_anchors_completion
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (cost : Sym2 (Fin (rule.generation (coarse + fine + 1)).vertices) → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin (rule.generation coarse).edges)
    (first last : Fin (rule.generation fine).vertices)
    (firstAvailable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine configuration edge)).Reachable (rule.generation fine).network.source first ∨
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
        (rule.generation fine).network.target first)
    (lastAvailable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine configuration edge)).Reachable (rule.generation fine).network.source last ∨
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
        (rule.generation fine).network.target last)
    (disconnected : ¬ ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine configuration edge)).Reachable first last)
    (reachable : ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Reachable
      ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex last)) :
    ∃ firstSide lastSide : Bool,
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
        (plantedVertex (rule.generation fine).network firstSide) first ∧
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
        (plantedVertex (rule.generation fine).network lastSide) last ∧
      weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph configuration) cost
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network firstSide))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex first) +
      weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph configuration) cost
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network lastSide))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex last) ≤
      weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph configuration) cost
        ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex last) := by
  let iso := generationBlockRawGraphIsoCompletion rule coarse fine configuration
  have rawReachable : ((rule.generation coarse).network.substitutedGraph (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration)).Reachable
      ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge first)
      ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge last) :=
    iso.reachable_iff.mp reachable
  obtain ⟨firstSide, lastSide, firstReachable, lastReachable, bound⟩ := weighted_cell_distinct_components_available_anchors_completion
    (rule.generation coarse).network (rule.generation fine).network (generationBlockCells rule coarse fine configuration)
    (fun bond => cost (bond.map iso)) (fun bond => nonnegative _) edge first last
    firstAvailable lastAvailable disconnected rawReachable
  refine ⟨firstSide, lastSide, firstReachable, lastReachable, ?_⟩
  simp_rw [← weightedDistance_graphIso iso cost nonnegative] at bound
  exact bound

end
end IGSIII34.ResistanceLimit

