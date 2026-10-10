import IGSIII.Geometry.CellLocalisationDiscrete
import IGSIII.Geometry.ActualBlockCellEmbedding

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution

/-- First-exit localisation on the actual indexed microscopic block, with
its original IGS II labels. -/
theorem generationBlockCellEmbedding_localisation (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (edge : Fin (rule.generation coarse).edges) (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable first last) :
    min (componentBoundaryDistance ((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine configuration edge))
        (rule.generation fine).network.source (rule.generation fine).network.target first)
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).dist first last : ℝ) ≤
      (((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
        ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
        ((generationBlockCellEmbedding rule coarse fine edge).vertex last) : ℝ) := by
  let cells := generationBlockCells rule coarse fine configuration
  have bound := intrinsic_cell_localisation (rule.generation coarse).network (rule.generation fine).network cells edge reachable
  have substitution_distance := iso_distance_eq_all
    ((rule.generation coarse).network.substitutionGraphIso (rule.generation fine).network cells)
    ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge first)
    ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge last)
  have block_distance := iso_distance_eq_all
    ((rule.generationBlockDecomposition coarse fine).openGraphIso configuration)
    ((generationBlockCellEmbedding rule coarse fine edge).vertex first)
    ((generationBlockCellEmbedding rule coarse fine edge).vertex last)
  have configuration_identity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
      substitutionConfigurationEquiv cells := by
    simp only [cells, generationBlockCells, generationBlockCellsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    ((rule.generationBlockDecomposition coarse fine).configuration configuration)).dist
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex first))
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex last)) = _ at block_distance
  rw [configuration_identity] at block_distance
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv cells)).dist
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge first))))
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge last)))) = _ at block_distance
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at block_distance
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv cells)).dist
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge first))
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge last)) = _ at substitution_distance
  rw [← substitution_distance, block_distance] at bound
  exact bound

end
end IGSIII.Geometry
