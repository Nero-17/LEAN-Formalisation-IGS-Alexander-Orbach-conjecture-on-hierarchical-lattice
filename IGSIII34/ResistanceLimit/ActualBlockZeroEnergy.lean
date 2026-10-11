import IGSIII34.ResistanceLimit.ActualSideCellZeroExtension
import IGSIII34.ResistanceLimit.ActualBlockZeroPersistence
import IGSIII34.ResistanceLimit.GenerationBlockEnergyCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem actual_block_zero_extension_source_energy
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (resistance : Fin (rule.generation (coarse + fine + 1)).edges → ℝ)
    (chosen : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (supplied : Fin (rule.generation fine).vertices → ℝ)
    (atSource : sourceProjection (sideNetwork (network (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration chosen)) sourceSide) supplied
      (rule.generation fine).network.source = 0)
    (atTarget : sourceProjection (sideNetwork (network (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration chosen)) sourceSide) supplied
      (rule.generation fine).network.target = 0)
    (anchorRetained : ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Reachable
      (rule.generation (coarse + fine + 1)).network.source
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex
        (sideNetwork (network (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration chosen)) sourceSide).source)) :
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration)
      (fun edge => resistance edge.val)
      (actualBlockZeroExtension rule coarse fine chosen
        (sourceProjection (sideNetwork (network (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration chosen)) sourceSide) supplied)) =
    sourceComponentEnergy (sideNetwork (network (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration chosen)) sourceSide)
      (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) supplied := by
  have configurationIdentity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  have indexedAnchor := anchorRetained.map
    ((rule.generationBlockDecomposition coarse fine).openGraphIso configuration).toHom
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    ((rule.generationBlockDecomposition coarse fine).configuration configuration)).Reachable
    ((rule.generationBlockDecomposition coarse fine).vertex (rule.generation (coarse + fine + 1)).network.source)
    ((rule.generationBlockDecomposition coarse fine).vertex
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex
        (sideNetwork (network (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration chosen)) sourceSide).source)) at indexedAnchor
  rw [(rule.generationBlockDecomposition coarse fine).source, configurationIdentity] at indexedAnchor
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration))).Reachable
    ((rule.generation coarse).network.substitute (rule.generation fine).network).source
    ((rule.generationBlockDecomposition coarse fine).vertex
      ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network chosen
          (sideNetwork (network (rule.generation fine).network
            (generationBlockCells rule coarse fine configuration chosen)) sourceSide).source)))) at indexedAnchor
  rw [Equiv.apply_symm_apply] at indexedAnchor
  have exactEnergy := actual_side_cellZeroExtension_source_energy
    (rule.generation coarse).network (rule.generation fine).network
    (generationBlockCells rule coarse fine configuration)
    (fun edge => resistance ((rule.generationBlockDecomposition coarse fine).edge.symm
      (finProdFinEquiv (edge.1, edge.2.val)))) chosen sourceSide supplied atSource atTarget indexedAnchor
  have transport := sourceComponentEnergy_network_equivalence (rule.generationBlockDecomposition coarse fine)
    configuration resistance
    (fun vertex => cellZeroExtension (rule.generation coarse).network (rule.generation fine).network chosen
      (sourceProjection (sideNetwork (network (rule.generation fine).network
        (generationBlockCells rule coarse fine configuration chosen)) sourceSide) supplied)
      ((Fintype.equivFin _).symm vertex))
  change _ = sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration)
    (fun edge => resistance edge.val)
    (actualBlockZeroExtension rule coarse fine chosen
      (sourceProjection (sideNetwork (network (rule.generation fine).network
        (generationBlockCells rule coarse fine configuration chosen)) sourceSide) supplied)) at transport
  rw [← transport, configurationIdentity]
  convert exactEnergy using 1
  · congr 1
    funext edge
    have reconstruction := congrArg Subtype.val ((substitutionOpenEdgeEquiv
      (generationBlockCells rule coarse fine configuration)).apply_symm_apply edge)
    change finProdFinEquiv _ = edge.val at reconstruction
    rw [← reconstruction]
  · rfl

end
end IGSIII34.ResistanceLimit
