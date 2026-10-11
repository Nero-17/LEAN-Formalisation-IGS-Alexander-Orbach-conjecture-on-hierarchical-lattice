import IGSIII34.ResistanceLimit.ActualBlockZeroEnergy
import IGSIII34.Forms.BlockZeroEnergyScaling
import IGSIII.Geometry.RootedComponentInclusion

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem stationary_block_zero_extension_energy
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (supplied : Fin (rule.generation fine).vertices → ℝ)
    (projection : sourceProjection (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide) supplied = supplied)
    (atSource : supplied (rule.generation fine).network.source = 0)
    (atTarget : supplied (rule.generation fine).network.target = 0)
    (anchorRetained : ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse chosen sourceSide)) :
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
      (fun edge => stationaryGenerationResistance rule field growth (coarse + fine + 1) [] edge.val)
      (actualBlockZeroExtension rule coarse fine chosen supplied) =
      growth ^ (coarse + 1) * sourceComponentEnergy (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
        (fun edge => stationaryGenerationResistance rule field growth fine
          (generationEdgeAddress rule coarse chosen) edge.val) supplied := by
  have cellsIdentity := generationBlockCells_marked rule marks coarse fine [] true chosen
  simp only [List.nil_append] at cellsIdentity
  have liftedAnchor : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
      (blockOldVertexEmbedding rule coarse fine (rule.generation coarse).network.source)
      (blockOldVertexEmbedding rule coarse fine (coarseCellPlantedVertex rule coarse chosen sourceSide)) := by
    apply (blockOldVertexEmbedding_reachable_iff rule coarse fine _ _ _).mpr
    rw [marked_generationBlockCoarse_eq rule marks crossing [] true coarse fine]
    exact anchorRetained
  have plantedIdentity : (generationBlockCellEmbedding rule coarse fine chosen).vertex
      (sideNetwork (network (rule.generation fine).network
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen)) sourceSide).source =
      blockOldVertexEmbedding rule coarse fine (coarseCellPlantedVertex rule coarse chosen sourceSide) := by
    rw [sideNetwork_network_source]
    cases sourceSide with
    | false => exact generationBlockCellEmbedding_target rule coarse fine chosen
    | true => exact generationBlockCellEmbedding_source rule coarse fine chosen
  have fineAnchor : ((rule.generation (coarse + fine + 1)).network.openGraph
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex
        (sideNetwork (network (rule.generation fine).network
          (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) chosen)) sourceSide).source) := by
    rw [plantedIdentity]
    have sourceIdentity := blockOldVertexEmbedding_planted rule coarse fine true
    change blockOldVertexEmbedding rule coarse fine (rule.generation coarse).network.source =
      (rule.generation (coarse + fine + 1)).network.source at sourceIdentity
    rw [sourceIdentity] at liftedAnchor
    exact liftedAnchor
  have equality := actual_block_zero_extension_source_energy rule coarse fine
    (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)
    (stationaryGenerationResistance rule field growth (coarse + fine + 1) []) chosen sourceSide supplied
    (by rw [cellsIdentity, projection]; exact atSource)
    (by rw [cellsIdentity, projection]; exact atTarget) fineAnchor
  rw [cellsIdentity, projection] at equality
  exact equality.trans (stationary_block_side_energy_scaling rule marks field growth coarse fine chosen
    (markedGenerationConfiguration rule marks coarse [] true chosen) sourceSide supplied)

end
end IGSIII34.ResistanceLimit
