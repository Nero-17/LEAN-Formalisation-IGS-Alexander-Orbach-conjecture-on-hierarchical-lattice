import IGSIII.Geometry.CellLocalisationSplitSeparation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The actual indexed microscopic version of noncrossing two-sided
separation, using one shared child configuration for its source and target. -/
theorem generationBlockCellEmbedding_noncrossing_boundary_separation (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (edge : Fin (rule.generation coarse).edges) (left right : Fin (rule.generation fine).vertices)
    (noncrossing : ¬ ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
      (rule.generation fine).network.source (rule.generation fine).network.target)
    (left_reached : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
      (rule.generation fine).network.source left)
    (right_reached : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge)).Reachable
      (rule.generation fine).network.target right)
    (reachable : ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Reachable
      ((generationBlockCellEmbedding rule coarse fine edge).vertex left)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex right)) :
    componentBoundaryDistance ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge))
      (rule.generation fine).network.source (rule.generation fine).network.target left +
    componentBoundaryDistance ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration edge))
      (rule.generation fine).network.source (rule.generation fine).network.target right ≤
    (((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
      ((generationBlockCellEmbedding rule coarse fine edge).vertex left)
      ((generationBlockCellEmbedding rule coarse fine edge).vertex right) : ℝ):= by
  let cells := generationBlockCells rule coarse fine configuration
  have configuration_identity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
      substitutionConfigurationEquiv cells := by
    simp only [cells, generationBlockCells, generationBlockCellsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  have block_reachable := reachable.map (((rule.generationBlockDecomposition coarse fine).openGraphIso configuration).toHom)
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    ((rule.generationBlockDecomposition coarse fine).configuration configuration)).Reachable
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex left))
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex right)) at block_reachable
  rw [configuration_identity] at block_reachable
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv cells)).Reachable
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge left))))
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge right)))) at block_reachable
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at block_reachable
  have raw_reachable : ((rule.generation coarse).network.substitutedGraph (rule.generation fine).network cells).Reachable
      ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge left)
      ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge right) :=
    (SimpleGraph.Iso.reachable_iff (φ := (rule.generation coarse).network.substitutionGraphIso (rule.generation fine).network cells)).mp block_reachable
  have bound := open_noncrossing_sides_boundary_separation (rule.generation coarse).network (rule.generation fine).network
    cells edge left right noncrossing left_reached right_reached raw_reachable
  have substitution_distance := iso_distance_eq_all
    ((rule.generation coarse).network.substitutionGraphIso (rule.generation fine).network cells)
    ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge left)
    ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge right)
  have block_distance := iso_distance_eq_all
    ((rule.generationBlockDecomposition coarse fine).openGraphIso configuration)
    ((generationBlockCellEmbedding rule coarse fine edge).vertex left)
    ((generationBlockCellEmbedding rule coarse fine edge).vertex right)
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    ((rule.generationBlockDecomposition coarse fine).configuration configuration)).dist
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex left))
      ((rule.generationBlockDecomposition coarse fine).vertex ((generationBlockCellEmbedding rule coarse fine edge).vertex right)) = _ at block_distance
  rw [configuration_identity] at block_distance
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv cells)).dist
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge left))))
      ((rule.generationBlockDecomposition coarse fine).vertex ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge right)))) = _ at block_distance
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at block_distance
  change (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
    (substitutionConfigurationEquiv cells)).dist
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge left))
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge right)) = _ at substitution_distance
  rw [← substitution_distance, block_distance] at bound
  exact bound

end
end IGSIII.Geometry

