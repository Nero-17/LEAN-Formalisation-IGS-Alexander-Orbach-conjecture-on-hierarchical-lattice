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

theorem actual_chemical_block_weighted_compatibility_completion20261011
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
    (coarse fine : ℕ)
    (first last : RetainedSkeletonVertex (rule.generation coarse).network (configuration coarse)) :
    weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph (configuration (coarse + fine + 1)))
      (indexedBondCost (rule.generation (coarse + fine + 1)).network (lengths (coarse + fine + 1)))
      (blockOldVertexEmbedding rule coarse fine first.val) (blockOldVertexEmbedding rule coarse fine last.val) =
    weightedDistance ((rule.generation coarse).network.openGraph (configuration coarse))
      (indexedBondCost (rule.generation coarse).network (lengths coarse)) first.val last.val := by
  have equality := congrArg₂ dist
    (actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      positive childConvergence coarse (coarse + fine + 1) (by omega) first)
    (actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      positive childConvergence coarse (coarse + fine + 1) (by omega) last)
  rw [actualChemicalVertex_distance, actualChemicalVertex_distance] at equality
  simpa only [retainedPersistentVertexEmbedding_val, ← blockOldVertexEmbedding_eq_persistent] using equality.symm

end
end IGSIII34.ResistanceLimit
