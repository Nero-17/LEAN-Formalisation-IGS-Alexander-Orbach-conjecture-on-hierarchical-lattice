import IGSIII34.ResistanceLimit.ActualChemicalLocalMeshCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalBlockAnchorsCompletion20261011
import IGSIII34.ResistanceLimit.ActualAvailableCellCoverCompletion20261011
import IGSIII.Geometry.ActualFiniteCluster

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5200000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

theorem actual_chemical_finite_birth_joint_anchor_completion20261011
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (beyond : start ≤ coarse)
    (point : ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (coarse + fine + 1)) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse [] true),
      dist point (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive coarse (coarse + fine + 1) (by omega) anchor) ≤ coefficient * eta ^ (coarse + 1) ∧
      dist (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence (coarse + fine + 1) point)
        (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence coarse anchor) ≤ coefficient * eta ^ (coarse + 1) := by
  obtain ⟨edge, child, side, identity, reachable, coarseRetained⟩ :=
    actual_retained_generation_available_cell_cover rule marks crossing coarse fine point.val point.property
  let anchor : RetainedSkeletonVertex (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse [] true) :=
    ⟨if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2,
      coarseRetained⟩
  obtain ⟨fineRetained, chemicalBound⟩ := actual_chemical_local_component_mesh_completion20261011
    rule classicalRule marks (fun depth => markedGenerationConfiguration rule marks depth [] true) (fun _ => rfl)
    coherent scale scalePositive lengths nonnegative positive childConvergence eta coefficient start radiusBounds
    coarse fine beyond edge side child reachable (identity ▸ point.property)
  have pointIdentity :
      (⟨(generationBlockCellEmbedding rule coarse fine edge).vertex child, identity ▸ point.property⟩ :
        RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) = point :=
    Subtype.ext identity.symm
  have anchorIdentity := actual_chemical_block_anchor_point_completion20261011 rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
    nonnegative positive childConvergence coarse fine edge side coarseRetained fineRetained
  rw [pointIdentity, ← anchorIdentity] at chemicalBound
  refine ⟨anchor, ?_, ?_⟩
  · have blockBound := generationBlockCellEmbedding_distance_to_planted_le rule coarse fine edge
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) side child reachable
    have blockBoundReal : (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex child) : ℝ) ≤
        (terminalComponentRadius (rule.generation fine).network (generationBlockCells rule coarse fine
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) : ℝ) := by
      exact_mod_cast blockBound
    have normalized := div_le_div_of_nonneg_right blockBoundReal (pow_pos scalePositive (coarse + fine + 2)).le
    have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse [] true edge) fine
      (by rw [generationEdgeAddress_length]; omega)
    rw [generationEdgeAddress_length] at cellRadius
    rw [generationBlockCells_marked, List.nil_append] at normalized
    have bound : (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex child) : ℝ) / scale ^ (coarse + fine + 2) ≤
        coefficient * eta ^ (coarse + 1) :=
      normalized.trans (by simpa only [markedTerminalComponentRadius, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)
    have plantedIdentity :
        (generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side) =
        persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) anchor.val := by
      cases side <;> simp only [anchor, plantedVertex, Bool.false_eq_true, ↓reduceIte,
        generationBlockCellEmbedding_source, generationBlockCellEmbedding_target, blockOldVertexEmbedding_eq_persistent]
    change (((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist point.val
      (persistentVertexEmbedding rule coarse (coarse + fine + 1) (by omega) anchor.val) : ℝ) /
      scale ^ (coarse + fine + 1 + 1) ≤ _
    rw [identity, SimpleGraph.dist_comm, ← plantedIdentity]
    convert bound using 1 <;> omega
  · simpa only [anchor, dist_comm] using chemicalBound

end
end IGSIII34.ResistanceLimit
