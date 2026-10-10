import IGSIII.Geometry.CellLocalisationSplitBlock
import IGSIII.Geometry.CellLocalisationIntrinsic

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
variable (coarse : ℕ) (edge : Fin (rule.generation coarse).edges)
variable (firstRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge true))
variable (componentLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (componentConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) edge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child)))

variable (closed : configuration coarse edge = false)
variable (secondRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse edge false))

include closed componentConvergence in
/-- Both retained sides of one actual noncrossing cell pay their intrinsic
boundary radii. Its source and target use the same raw configuration tower. -/
theorem actualComponentFiniteInclusion_noncrossing_boundary_separation (fine : ℕ)
    (first : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) true)
    (last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge) false) :
    weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
      (indexedBondCost (rule.generation fine).network (componentLengths fine))
      (rule.generation fine).network.source (rule.generation fine).network.target first.val +
    weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge))
      (indexedBondCost (rule.generation fine).network (componentLengths fine))
      (rule.generation fine).network.source (rule.generation fine).network.target last.val ≤
    dist (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse edge true firstRetained fine first)
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse edge false secondRetained fine last):= by
  let firstConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) edge
  let secondConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) edge
  have firstCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse edge
  have secondCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse edge
  have firstIncluded := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge true firstRetained first).property
  have lastIncluded := (retainedBlockComponentEmbedding rule configuration coherent coarse fine edge false secondRetained last).property
  have ambientLimit := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    (coarse + fine + 1) (ambientLengths (coarse + fine + 1)) (ambientConvergence (coarse + fine + 1))
    (firstIncluded.symm.trans lastIncluded)).comp (tendsto_add_atTop_nat (coarse + 1))
  have firstBoundaryLimit := actual_persistent_boundary_distances_tendsto rule classicalRule firstConfiguration firstCoherent
    scale scalePositive (coarse + 1) fine componentLengths componentConvergence first.val
  have secondBoundaryLimit := actual_persistent_boundary_distances_tendsto rule classicalRule secondConfiguration secondCoherent
    scale scalePositive (coarse + 1) fine componentLengths componentConvergence last.val
  rw [actualComponentFiniteInclusion, actualComponentFiniteInclusion, actualChemicalVertex_distance]
  apply le_of_tendsto_of_tendsto (firstBoundaryLimit.add secondBoundaryLimit) ambientLimit
  filter_upwards [eventually_ge_atTop fine] with host beyond
  dsimp only [Function.comp_apply]
  rw [show host + (coarse + 1) = coarse + host + 1 by omega]
  simp only [persistentNormalizedBoundaryDistance, persistentNormalizedDistance,
    dif_pos (show coarse + fine + 1 ≤ coarse + host + 1 by omega), dif_pos beyond]
  change
    componentBoundaryDistance ((rule.generation host).network.openGraph (firstConfiguration host))
      (rule.generation host).network.source (rule.generation host).network.target
      (persistentVertexEmbedding rule fine host beyond first.val) / scale ^ (host + 1) / scale ^ (coarse + 1) +
    componentBoundaryDistance ((rule.generation host).network.openGraph (secondConfiguration host))
      (rule.generation host).network.source (rule.generation host).network.target
      (persistentVertexEmbedding rule fine host beyond last.val) / scale ^ (host + 1) / scale ^ (coarse + 1) ≤
    (((rule.generation (coarse + host + 1)).network.openGraph (configuration (coarse + host + 1))).dist
      (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex first.val))
      (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex last.val)) : ℝ) / scale ^ (coarse + host + 1 + 1)
  have reached := (persistentVertexEmbedding_reachable_iff rule configuration coherent
    (coarse + fine + 1) (coarse + host + 1) (by omega) _ _).mpr (firstIncluded.symm.trans lastIncluded)
  dsimp only [retainedBlockComponentEmbedding, Function.Embedding.coeFn_mk] at reached
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond edge first.val,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond edge last.val] at reached ⊢
  have childNoncrossing : ¬ ((rule.generation host).network.openGraph (firstConfiguration host)).Reachable
      (rule.generation host).network.source (rule.generation host).network.target := by
    intro connected
    have crossed := ((rule.generation host).network.crosses_eq_true _).mpr connected
    change generationBlockCoarse rule coarse host (configuration (coarse + host + 1)) edge = true at crossed
    rw [generationBlockCoarse_of_coherent rule configuration coherent coarse host, closed] at crossed
    exact Bool.false_ne_true crossed
  have sourceReached : ((rule.generation host).network.openGraph (firstConfiguration host)).Reachable
      (rule.generation host).network.source (persistentVertexEmbedding rule fine host beyond first.val) :=
    (retainedComponentPersistentEmbedding rule firstConfiguration firstCoherent true fine host beyond first).property
  have targetReached : ((rule.generation host).network.openGraph (firstConfiguration host)).Reachable
      (rule.generation host).network.target (persistentVertexEmbedding rule fine host beyond last.val) :=
    (retainedComponentPersistentEmbedding rule firstConfiguration firstCoherent false fine host beyond last).property
  have graphBound := generationBlockCellEmbedding_noncrossing_boundary_separation rule coarse host (configuration (coarse + host + 1))
    edge (persistentVertexEmbedding rule fine host beyond first.val)
    (persistentVertexEmbedding rule fine host beyond last.val) childNoncrossing sourceReached targetReached reached
  rw [← add_div, ← add_div, div_div]
  have denominatorIdentity : scale ^ (host + 1) * scale ^ (coarse + 1) = scale ^ (coarse + host + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [denominatorIdentity]
  exact div_le_div_of_nonneg_right graphBound (pow_pos scalePositive (coarse + host + 1 + 1)).le

end
end IGSIII.Geometry

