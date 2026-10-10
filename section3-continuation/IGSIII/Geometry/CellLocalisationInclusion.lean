import IGSIII.Geometry.CellLocalisationBoundaryLimit
import IGSIII.Geometry.RootedComponentInclusion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (ambientLengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
variable (ambientNonnegative : ∀ depth edge, 0 ≤ ambientLengths depth edge)
variable (ambientPositive : ∀ depth edge, configuration depth edge = true → 0 < ambientLengths depth edge)
variable (ambientConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (ambientLengths coarse edge)))
variable (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) (sourceSide : Bool)
variable (anchorRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge sourceSide))
variable (componentLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (componentConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) edge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child)))

include componentConvergence in
/-- The actual intrinsic component inclusion satisfies the boundary cone
inequality, obtained from the very same microscopic graphs as its two metrics. -/
theorem actualComponentFiniteInclusion_localisation (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) sourceSide) :
    min (weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
      (indexedBondCost (rule.generation fine).network (componentLengths fine))
      (rule.generation fine).network.source (rule.generation fine).network.target first.val)
      (weightedDistance ((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
        (indexedBondCost (rule.generation fine).network (componentLengths fine)) first.val last.val) ≤
    dist (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge sourceSide anchorRetained fine first)
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse edge sourceSide anchorRetained fine last) := by
  let childConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) edge
  have childCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse edge
  have firstRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained first).property
  have lastRetained := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge sourceSide anchorRetained last).property
  have ambientLimit := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    (coarse + fine + 1) (ambientLengths (coarse + fine + 1)) (ambientConvergence (coarse + fine + 1))
    (firstRetained.symm.trans lastRetained)).comp (tendsto_add_atTop_nat (coarse + 1))
  have childLimit := actual_persistent_skeleton_distances_tendsto_offset rule classicalRule childConfiguration childCoherent scale scalePositive
    (coarse + 1) fine componentLengths componentConvergence (first.property.symm.trans last.property)
  have boundaryLimit := actual_persistent_boundary_distances_tendsto rule classicalRule childConfiguration childCoherent
    scale scalePositive (coarse + 1) fine componentLengths componentConvergence first.val
  rw [actualComponentFiniteInclusion, actualComponentFiniteInclusion, actualChemicalVertex_distance]
  apply le_of_tendsto_of_tendsto (boundaryLimit.min childLimit) ambientLimit
  filter_upwards [eventually_ge_atTop fine] with host beyond
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedBoundaryDistance, persistentNormalizedDistance,
    dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega), dif_pos beyond]
  change min
    (componentBoundaryDistance ((rule.generation host).network.openGraph (childConfiguration host))
      (rule.generation host).network.source (rule.generation host).network.target
      (persistentVertexEmbedding rule fine host beyond first.val) / scale ^ (host + 1) / scale ^ (coarse + 1))
    ((((rule.generation host).network.openGraph (childConfiguration host)).dist
      (persistentVertexEmbedding rule fine host beyond first.val)
      (persistentVertexEmbedding rule fine host beyond last.val) : ℝ) / scale ^ (host + 1) / scale ^ (coarse + 1)) ≤
    (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
      (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex first.val))
      (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex last.val)) : ℝ) / scale ^ (coarse + host + 1 + 1)
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge first.val,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge last.val]
  have reached := (persistentVertexEmbedding_reachable_iff rule childConfiguration childCoherent fine host beyond first.val last.val).mpr
    (first.property.symm.trans last.property)
  have graphBound := generationBlockCellEmbedding_localisation rule coarse host (configuration (coarse + host + 1)) edge
    (persistentVertexEmbedding rule fine host beyond first.val) (persistentVertexEmbedding rule fine host beyond last.val) reached
  rw [min_div_div_right (pow_pos scalePositive (coarse + 1)).le,
    min_div_div_right (pow_pos scalePositive (host + 1)).le, div_div]
  have denominatorIdentity : scale ^ (host + 1) * scale ^ (coarse + 1) = scale ^ (coarse + host + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [denominatorIdentity]
  exact div_le_div_of_nonneg_right graphBound (pow_pos scalePositive (coarse + host + 1 + 1)).le

end
end IGSIII.Geometry

