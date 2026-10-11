import IGSIII.Geometry.ActualChemicalSkeleton
import IGSIII.Geometry.ActualBlockCellEmbedding

/-! Exact chemical metric compatibility across arbitrary actual blocks,
derived from the original normalized microscopic chemical-distance limits. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

theorem actual_chemical_block_anchor_point_completion20261011
    (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (positive : ∀ depth edge, configuration depth edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (coarse fine : ℕ) (edge : Fin (rule.generation coarse).edges) (side : Bool)
    (coarseRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
      (rule.generation coarse).network.source
      (if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2))
    (fineRetained : ((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1))).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))) :
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence coarse
      ⟨if side then ((rule.generation coarse).network.endpoint edge).1 else ((rule.generation coarse).network.endpoint edge).2,coarseRetained⟩ =
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
      (coarse + fine + 1) ⟨_,fineRetained⟩ := by
  rw [actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
    coarse (coarse + fine + 1) (by omega)]
  apply congrArg (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
    (coarse + fine + 1))
  apply Subtype.ext
  rw [retainedPersistentVertexEmbedding_val]
  cases side <;> simp only [plantedVertex, Bool.false_eq_true, ↓reduceIte, generationBlockCellEmbedding_source,
    generationBlockCellEmbedding_target, blockOldVertexEmbedding_eq_persistent]

end
end IGSIII34.ResistanceLimit
