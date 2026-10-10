import IGSIII.Geometry.ActualBlockCellEmbedding
import IGSIII.Geometry.ActualChemicalSkeleton

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

theorem generationBlockCells_sequence_coherent (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
    configurationSequenceCoherent rule (fun fine =>
      generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) := by
  intro fine
  rw [← generationBlockCells_coarsen]
  exact congrArg (fun value => generationBlockCells rule coarse fine value edge)
    (coherent (coarse + fine + 1))

/-- A bound on the actual microscopic component persists in the actual
chemical completion. Both endpoints are concrete retained vertices. -/
theorem actualChemicalVertex_dist_block_le (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale)
    (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
    (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
    (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))
    (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) (source_side : Bool)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).Reachable
        (plantedVertex (rule.generation fine).network source_side) vertex)
    (anchor_retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (configuration (coarse + fine + 1))).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine edge).vertex
          (plantedVertex (rule.generation fine).network source_side)))
    (vertex_retained : ((rule.generation (coarse + fine + 1)).network.openGraph
      (configuration (coarse + fine + 1))).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex))
    (bound : ℝ)
    (microscopic_bound : ∀ host (point : Fin (rule.generation host).vertices),
      ((rule.generation host).network.openGraph
        (generationBlockCells rule coarse host (configuration (coarse + host + 1)) edge)).Reachable
          (plantedVertex (rule.generation host).network source_side) point →
      (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
        ((generationBlockCellEmbedding rule coarse host edge).vertex
          (plantedVertex (rule.generation host).network source_side))
        ((generationBlockCellEmbedding rule coarse host edge).vertex point) : ℝ) /
        scale ^ (coarse + host + 2) ≤ bound) :
    dist
      (actualChemicalVertex rule classicalRule configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence (coarse + fine + 1)
          ⟨_, anchor_retained⟩)
      (actualChemicalVertex rule classicalRule configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence (coarse + fine + 1)
          ⟨_, vertex_retained⟩) ≤ bound := by
  rw [actualChemicalVertex_distance]
  have convergence := (actual_persistent_skeleton_distances_tendsto rule classicalRule
    configuration coherent scale scale_positive (coarse + fine + 1)
    (limit_length (coarse + fine + 1)) (child_convergence (coarse + fine + 1))
    (anchor_retained.symm.trans vertex_retained)).comp (tendsto_add_atTop_nat (coarse + 1))
  apply le_of_tendsto convergence
  filter_upwards [eventually_ge_atTop fine] with host beyond
  have child_reachable := (persistentVertexEmbedding_reachable_iff rule
    (fun depth => generationBlockCells rule coarse depth (configuration (coarse + depth + 1)) edge)
    (generationBlockCells_sequence_coherent rule configuration coherent coarse edge)
    fine host beyond (plantedVertex (rule.generation fine).network source_side) vertex).mpr reachable
  rw [persistentVertexEmbedding_planted] at child_reachable
  have estimate := microscopic_bound host (persistentVertexEmbedding rule fine host beyond vertex) child_reachable
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedDistance, dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega)]
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge _,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge _,
    persistentVertexEmbedding_planted]
  simpa only [Nat.add_assoc] using estimate

end
end IGSIII.Geometry
