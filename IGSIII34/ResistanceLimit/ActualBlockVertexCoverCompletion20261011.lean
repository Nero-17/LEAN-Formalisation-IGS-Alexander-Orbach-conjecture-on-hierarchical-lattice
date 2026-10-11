import IGSIII34.ResistanceLimit.GenerationBlockFlatnessCompletion20261011

/-! Every actual retained finite vertex is either a genuine persistent
coarse vertex or a vertex of a block component connected to an available
terminal. No exceptional set or empirical-mass approximation is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem actual_retained_generation_block_cover
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (vertex : Fin (rule.generation (coarse + fine + 1)).vertices)
    (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
      (rule.generation (coarse + fine + 1)).network.source vertex) :
    (∃ old : Fin (rule.generation coarse).vertices,
      ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse address opened)).Reachable
        (rule.generation coarse).network.source old ∧ vertex = blockOldVertexEmbedding rule coarse fine old) ∨
    (∃ edge : Fin (rule.generation coarse).edges, ∃ child : Fin (rule.generation fine).vertices,
      vertex = (generationBlockCellEmbedding rule coarse fine edge).vertex child ∧
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
        (rule.generation fine).network.source child ∨
       ((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).Reachable
        (rule.generation fine).network.target child)) := by
  let raw : (rule.generation coarse).network.SubstitutionVertex (rule.generation fine).network :=
    (Fintype.equivFin _).symm ((rule.generationBlockDecomposition coarse fine).vertex vertex)
  have reconstruction : (rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ raw) = vertex := by
    simp only [raw, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have rawRetained := (marked_generation_block_source_retained_iff rule marks coarse fine address opened raw).mp
    (by simpa only [reconstruction] using retained)
  cases rawIdentity : raw with
  | inl old =>
      left
      have coarseRetained := ((rule.generation coarse).network.substitutedReachable_iff
        (rule.generation fine).network
        (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge)) _ old).mp
          (by simpa only [rawIdentity] using rawRetained)
      rw [stationary_block_coarsens rule marks crossing
        (fun edge => address ++ generationEdgeAddress rule coarse edge)
        (markedGenerationConfiguration rule marks coarse address opened) fine] at coarseRetained
      exact ⟨old, coarseRetained, (by simpa only [rawIdentity, blockOldVertexEmbedding,
        Function.Embedding.coeFn_mk] using reconstruction.symm)⟩
  | inr cell =>
      right
      have active := ((rule.generation coarse).network.substitutedReachable_iff_active
        (rule.generation fine).network
        (fun edge => markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge)
          (markedGenerationConfiguration rule marks coarse address opened edge))
        (rule.generation coarse).network.source raw).mp rawRetained
      rw [rawIdentity] at active
      change (_ ∧ ((rule.generation fine).network.openGraph
        (markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse cell.1)
          (markedGenerationConfiguration rule marks coarse address opened cell.1))).Reachable
          (rule.generation fine).network.source cell.2.val) ∨
        (_ ∧ ((rule.generation fine).network.openGraph
        (markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse cell.1)
          (markedGenerationConfiguration rule marks coarse address opened cell.1))).Reachable
          (rule.generation fine).network.target cell.2.val) at active
      have childReconstruction : vertex = (generationBlockCellEmbedding rule coarse fine cell.1).vertex cell.2.val := by
        rw [← reconstruction, rawIdentity]
        change _ = (rule.generationBlockDecomposition coarse fine).vertex.symm
          (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network cell.1 cell.2.val))
        simp only [cellVertex, dif_neg cell.2.property.1, dif_neg cell.2.property.2]
        rfl
      refine ⟨cell.1, cell.2.val, childReconstruction, ?_⟩
      rw [generationBlockCells_marked]
      exact active.elim (fun fromSource => Or.inl fromSource.2) (fun fromTarget => Or.inr fromTarget.2)

end
end IGSIII34.ResistanceLimit
