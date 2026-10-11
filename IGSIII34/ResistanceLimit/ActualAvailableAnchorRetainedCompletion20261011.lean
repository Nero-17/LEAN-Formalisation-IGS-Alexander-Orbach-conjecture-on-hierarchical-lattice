import IGSIII34.ResistanceLimit.ActualAvailableCellCoverCompletion20261011

/-! Every locally available terminal of an actual retained block point is
retained in the coarse source cluster. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem actual_available_block_anchor_retained_completion20261011
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (child : Fin (rule.generation fine).vertices)
    (localReachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
      (plantedVertex (rule.generation fine).network side) child)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine edge).vertex child)) :
    ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse address opened)).Reachable
      (rule.generation coarse).network.source
      (if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2) := by
  have mapped := localReachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
    (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))
  have anchorRetained := retained.trans (by
    simpa only [generationBlockCellEmbedding_openGraphHom_apply] using mapped.symm)
  cases side with
  | false =>
      rw [show plantedVertex (rule.generation fine).network false = (rule.generation fine).network.target by rfl,
        generationBlockCellEmbedding_target] at anchorRetained
      exact (actual_block_old_retained_iff rule marks crossing coarse fine address opened _).mp anchorRetained
  | true =>
      rw [show plantedVertex (rule.generation fine).network true = (rule.generation fine).network.source by rfl,
        generationBlockCellEmbedding_source] at anchorRetained
      exact (actual_block_old_retained_iff rule marks crossing coarse fine address opened _).mp anchorRetained

end
end IGSIII34.ResistanceLimit
