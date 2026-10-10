import IGSIII.Geometry.CellLocalisationInclusion
import IGSIII.Geometry.CellLocalisationBlockSeparation

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
variable (coarse : ℕ)
variable (firstEdge secondEdge : Fin (rule.generation coarse).edges) (distinct : firstEdge ≠ secondEdge)
variable (firstSide secondSide : Bool)
variable (firstRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse firstEdge firstSide))
variable (secondRetained : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable
  (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse secondEdge secondSide))
variable (firstLengths secondLengths : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (firstConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) firstEdge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (firstLengths age child)))
variable (secondConvergence : ∀ age child, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule age fine
      (generationBlockCells rule coarse (age + fine + 1) (configuration (coarse + (age + fine + 1) + 1)) secondEdge) child)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (secondLengths age child)))

include distinct firstConvergence secondConvergence in
/-- The sum of two intrinsic boundary radii survives in the actual ambient
completion, including either retained side of a shared noncrossing cell. -/
theorem actualComponentFiniteInclusion_boundary_separation (fine : ℕ)
    (first : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge) firstSide)
    (last : RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge) secondSide) :
    weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) firstEdge))
      (indexedBondCost (rule.generation fine).network (firstLengths fine))
      (rule.generation fine).network.source (rule.generation fine).network.target first.val +
    weightedComponentBoundaryDistance ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) secondEdge))
      (indexedBondCost (rule.generation fine).network (secondLengths fine))
      (rule.generation fine).network.source (rule.generation fine).network.target last.val ≤
    dist (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
      ambientConvergence coarse firstEdge firstSide firstRetained fine first)
      (actualComponentFiniteInclusion rule classicalRule configuration coherent scale scalePositive ambientLengths ambientNonnegative ambientPositive
        ambientConvergence coarse secondEdge secondSide secondRetained fine last) := by
  let firstConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) firstEdge
  let secondConfiguration := fun age => generationBlockCells rule coarse age (configuration (coarse + age + 1)) secondEdge
  have firstCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse firstEdge
  have secondCoherent := generationBlockCells_sequence_coherent rule configuration coherent coarse secondEdge
  have firstIncluded := (retainedBlockComponentEmbedding rule configuration coherent coarse fine firstEdge firstSide firstRetained first).property
  have lastIncluded := (retainedBlockComponentEmbedding rule configuration coherent coarse fine secondEdge secondSide secondRetained last).property
  have ambientLimit := (actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    (coarse + fine + 1) (ambientLengths (coarse + fine + 1)) (ambientConvergence (coarse + fine + 1))
    (firstIncluded.symm.trans lastIncluded)).comp (tendsto_add_atTop_nat (coarse + 1))
  have firstBoundaryLimit := actual_persistent_boundary_distances_tendsto rule classicalRule firstConfiguration firstCoherent
    scale scalePositive (coarse + 1) fine firstLengths firstConvergence first.val
  have secondBoundaryLimit := actual_persistent_boundary_distances_tendsto rule classicalRule secondConfiguration secondCoherent
    scale scalePositive (coarse + 1) fine secondLengths secondConvergence last.val
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
        ((generationBlockCellEmbedding rule coarse fine firstEdge).vertex first.val))
      (persistentVertexEmbedding rule (coarse + fine + 1) (coarse + host + 1) (by omega)
        ((generationBlockCellEmbedding rule coarse fine secondEdge).vertex last.val)) : ℝ) / scale ^ (coarse + host + 1 + 1)
  have reached := (persistentVertexEmbedding_reachable_iff rule configuration coherent
    (coarse + fine + 1) (coarse + host + 1) (by omega) _ _).mpr (firstIncluded.symm.trans lastIncluded)
  dsimp only [retainedBlockComponentEmbedding, Function.Embedding.coeFn_mk] at reached
  rw [generationBlockCellEmbedding_persistent rule coarse fine host beyond firstEdge first.val,
    generationBlockCellEmbedding_persistent rule coarse fine host beyond secondEdge last.val] at reached ⊢
  have graphBound := generationBlockCellEmbedding_boundary_separation rule coarse host (configuration (coarse + host + 1))
    firstEdge secondEdge distinct (persistentVertexEmbedding rule fine host beyond first.val)
    (persistentVertexEmbedding rule fine host beyond last.val) reached
  rw [← add_div, ← add_div, div_div]
  have denominatorIdentity : scale ^ (host + 1) * scale ^ (coarse + 1) = scale ^ (coarse + host + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [denominatorIdentity]
  exact div_le_div_of_nonneg_right graphBound (pow_pos scalePositive (coarse + host + 1 + 1)).le

end
end IGSIII.Geometry

