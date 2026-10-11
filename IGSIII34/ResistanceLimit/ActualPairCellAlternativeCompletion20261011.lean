import IGSIII34.ResistanceLimit.ActualAvailableAnchorRetainedCompletion20261011
import IGSIII34.ResistanceLimit.GenerationSplitAnchorsCompletion20261011

/-! A complete two-point alternative on the actual retained generation.
Points share one available component, or they pay the chemical costs of
reaching genuinely retained coarse anchors. No frontier is discarded. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem actual_retained_pair_cell_alternative_completion20261011
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ)
    (cost : Sym2 (Fin (rule.generation (coarse + fine + 1)).vertices) → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    (first last : Fin (rule.generation (coarse + fine + 1)).vertices)
    (firstRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
      (rule.generation (coarse + fine + 1)).network.source first)
    (lastRetained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
      (rule.generation (coarse + fine + 1)).network.source last) :
    (∃ edge : Fin (rule.generation coarse).edges,
      ∃ left right : Fin (rule.generation fine).vertices, ∃ side : Bool,
        first = (generationBlockCellEmbedding rule coarse fine edge).vertex left ∧
        last = (generationBlockCellEmbedding rule coarse fine edge).vertex right ∧
        ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) left ∧
        ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) right ∧
        ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
          (rule.generation coarse).network.source
          (if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2)) ∨
    (∃ firstEdge lastEdge : Fin (rule.generation coarse).edges,
      ∃ left right : Fin (rule.generation fine).vertices, ∃ firstSide lastSide : Bool,
        first = (generationBlockCellEmbedding rule coarse fine firstEdge).vertex left ∧
        last = (generationBlockCellEmbedding rule coarse fine lastEdge).vertex right ∧
        ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) firstEdge)).Reachable
          (plantedVertex (rule.generation fine).network firstSide) left ∧
        ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) lastEdge)).Reachable
          (plantedVertex (rule.generation fine).network lastSide) right ∧
        ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
          (rule.generation coarse).network.source
          (if firstSide then ((rule.generation coarse).network.endpoint firstEdge).1 else ((rule.generation coarse).network.endpoint firstEdge).2) ∧
        ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
          (rule.generation coarse).network.source
          (if lastSide then ((rule.generation coarse).network.endpoint lastEdge).1 else ((rule.generation coarse).network.endpoint lastEdge).2) ∧
        weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) cost
          ((generationBlockCellEmbedding rule coarse fine firstEdge).vertex (plantedVertex (rule.generation fine).network firstSide)) first +
        weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) cost
          ((generationBlockCellEmbedding rule coarse fine lastEdge).vertex (plantedVertex (rule.generation fine).network lastSide)) last ≤
        weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) cost first last) := by
  obtain ⟨firstEdge, left, firstSide, firstIdentity, firstReachable, firstAnchorRetained⟩ :=
    actual_retained_generation_available_cell_cover rule marks crossing coarse fine first firstRetained
  obtain ⟨lastEdge, right, lastSide, lastIdentity, lastReachable, lastAnchorRetained⟩ :=
    actual_retained_generation_available_cell_cover rule marks crossing coarse fine last lastRetained
  have firstAvailable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) firstEdge)).Reachable
      (rule.generation fine).network.source left ∨
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) firstEdge)).Reachable
      (rule.generation fine).network.target left := by
    cases firstSide
    · exact Or.inr firstReachable
    · exact Or.inl firstReachable
  have lastAvailable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) lastEdge)).Reachable
      (rule.generation fine).network.source right ∨
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) lastEdge)).Reachable
      (rule.generation fine).network.target right := by
    cases lastSide
    · exact Or.inr lastReachable
    · exact Or.inl lastReachable
  have pairReachable := firstRetained.symm.trans lastRetained
  rw [firstIdentity, lastIdentity] at pairReachable
  by_cases sameEdge : firstEdge = lastEdge
  · subst lastEdge
    by_cases sameComponent : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) firstEdge)).Reachable left right
    · exact Or.inl ⟨firstEdge, left, right, firstSide, firstIdentity, lastIdentity,
        firstReachable, firstReachable.trans sameComponent, firstAnchorRetained⟩
    · obtain ⟨newFirstSide, newLastSide, newFirstReachable, newLastReachable, bound⟩ :=
        generation_block_distinct_components_available_anchors_completion20261011 rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) cost nonnegative firstEdge left right
          firstAvailable lastAvailable sameComponent pairReachable
      exact Or.inr ⟨firstEdge, firstEdge, left, right, newFirstSide, newLastSide, firstIdentity, lastIdentity,
        newFirstReachable, newLastReachable,
        actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine [] true firstEdge
          newFirstSide left newFirstReachable (firstIdentity ▸ firstRetained),
        actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine [] true firstEdge
          newLastSide right newLastReachable (lastIdentity ▸ lastRetained),
        by simpa only [firstIdentity, lastIdentity] using bound⟩
  · obtain ⟨newFirstSide, newLastSide, newFirstReachable, newLastReachable, bound⟩ :=
      generation_block_distinct_cells_available_anchors_completion20261011 rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) cost nonnegative firstEdge lastEdge sameEdge
        left right firstAvailable lastAvailable pairReachable
    exact Or.inr ⟨firstEdge, lastEdge, left, right, newFirstSide, newLastSide, firstIdentity, lastIdentity,
      newFirstReachable, newLastReachable,
      actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine [] true firstEdge
        newFirstSide left newFirstReachable (firstIdentity ▸ firstRetained),
      actual_available_block_anchor_retained_completion20261011 rule marks crossing coarse fine [] true lastEdge
        newLastSide right newLastReachable (lastIdentity ▸ lastRetained),
      by simpa only [firstIdentity, lastIdentity] using bound⟩

end
end IGSIII34.ResistanceLimit
