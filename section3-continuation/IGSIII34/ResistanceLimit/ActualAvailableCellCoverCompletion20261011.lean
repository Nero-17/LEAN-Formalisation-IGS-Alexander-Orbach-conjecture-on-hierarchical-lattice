import IGSIII34.ResistanceLimit.ActualBlockVertexCoverCompletion20261011
import IGSIII.Geometry.PositiveCylinderAnchors

/-! A complete available-cell cover of the actual finite cluster, including
the persistent coarse vertices. Each selected anchor is genuinely retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem actual_block_old_retained_iff
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (vertex : Fin (rule.generation coarse).vertices) :
    ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source (blockOldVertexEmbedding rule coarse fine vertex) ↔
    ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse address opened)).Reachable
      (rule.generation coarse).network.source vertex := by
  have raw := marked_generation_block_source_retained_iff rule marks coarse fine address opened (Sum.inl vertex)
  have descended := (rule.generation coarse).network.substitutedReachable_iff (rule.generation fine).network
    (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse address opened edge)) (rule.generation coarse).network.source vertex
  rw [stationary_block_coarsens rule marks crossing (fun edge => address ++ generationEdgeAddress rule coarse edge)
    (markedGenerationConfiguration rule marks coarse address opened) fine] at descended
  exact raw.trans descended

theorem actual_retained_generation_available_cell_cover
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ) (vertex : Fin (rule.generation (coarse + fine + 1)).vertices)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
      (rule.generation (coarse + fine + 1)).network.source vertex) :
    ∃ edge : Fin (rule.generation coarse).edges, ∃ child : Fin (rule.generation fine).vertices, ∃ side : Bool,
      vertex = (generationBlockCellEmbedding rule coarse fine edge).vertex child ∧
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
        (plantedVertex (rule.generation fine).network side) child ∧
      ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
        (rule.generation coarse).network.source
          (if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2) := by
  rcases actual_retained_generation_block_cover rule marks crossing coarse fine [] true vertex retained with
    ⟨old, oldRetained, identity⟩ | ⟨edge, child, identity, available⟩
  · obtain ⟨edge, opened, sourceRetained, targetRetained, endpoint⟩ := retained_vertex_incident_open_edge
      (rule.generation coarse).network (markedGenerationConfiguration rule marks coarse [] true)
      (markedGenerationConfiguration_crosses rule marks crossing coarse [] true) old oldRetained
    rcases endpoint with atSource | atTarget
    · refine ⟨edge, (rule.generation fine).network.source, true, ?_, SimpleGraph.Reachable.refl _, ?_⟩
      · rw [generationBlockCellEmbedding_source, ← atSource]
        exact identity
      · exact sourceRetained
    · refine ⟨edge, (rule.generation fine).network.target, false, ?_, SimpleGraph.Reachable.refl _, ?_⟩
      · rw [generationBlockCellEmbedding_target, ← atTarget]
        exact identity
      · exact targetRetained
  · have terminalRetained (side : Bool)
        (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) child) :
        ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
          (rule.generation coarse).network.source
            (if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2) := by
      have mapped := reachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
      have anchorRetained := retained.trans (by simpa only [identity, generationBlockCellEmbedding_openGraphHom_apply] using mapped.symm)
      cases side with
      | false =>
          rw [show plantedVertex (rule.generation fine).network false = (rule.generation fine).network.target by rfl,
            generationBlockCellEmbedding_target] at anchorRetained
          exact (actual_block_old_retained_iff rule marks crossing coarse fine [] true _).mp anchorRetained
      | true =>
          rw [show plantedVertex (rule.generation fine).network true = (rule.generation fine).network.source by rfl,
            generationBlockCellEmbedding_source] at anchorRetained
          exact (actual_block_old_retained_iff rule marks crossing coarse fine [] true _).mp anchorRetained
    rcases available with sourceAvailable | targetAvailable
    · exact ⟨edge, child, true, identity, sourceAvailable, terminalRetained true sourceAvailable⟩
    · exact ⟨edge, child, false, identity, targetAvailable, terminalRetained false targetAvailable⟩

end
end IGSIII34.ResistanceLimit
