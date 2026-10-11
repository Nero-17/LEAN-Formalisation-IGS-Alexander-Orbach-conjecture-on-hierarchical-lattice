import IGSIII.Geometry.CellLocalisationRelabelling
import IGSIII.Geometry.CellLocalisationBlockSeparation

/-! Exact weighted-distance transport for arbitrary actual IGS generation
blocks. Bond costs remain the original ambient costs throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

def generationBlockRawGraphIsoCompletion20261011 (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    ((rule.generation coarse).network.substitutedGraph (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration)) ≃g
    ((rule.generation (coarse + fine + 1)).network.openGraph configuration) where
  toEquiv := (Fintype.equivFin _).trans (rule.generationBlockDecomposition coarse fine).vertex.symm
  map_rel_iff' := by
    intro first last
    have identity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
        substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) := by
      simp only [generationBlockCells, generationBlockCellsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    have blockAdj := (((rule.generationBlockDecomposition coarse fine).openGraphIso configuration).symm).map_rel_iff
      (a := Fintype.equivFin _ first) (b := Fintype.equivFin _ last)
    change ((rule.generation (coarse + fine + 1)).network.openGraph configuration).Adj
      ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ first))
      ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ last)) ↔
      (((rule.generation coarse).network.substitute (rule.generation fine).network).openGraph
        ((rule.generationBlockDecomposition coarse fine).configuration configuration)).Adj
        (Fintype.equivFin _ first) (Fintype.equivFin _ last) at blockAdj
    rw [identity] at blockAdj
    exact blockAdj.trans (((rule.generation coarse).network.substitutionGraphIso (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration)).map_rel_iff (a := first) (b := last))

theorem generationBlockRawGraphIso_apply_completion20261011 (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (point : (rule.generation coarse).network.SubstitutionVertex (rule.generation fine).network) :
    generationBlockRawGraphIsoCompletion20261011 rule coarse fine configuration point =
      (rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ point) := by
  rfl

theorem generationBlockRawGraphIso_cell_completion20261011 (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (edge : Fin (rule.generation coarse).edges) (point : Fin (rule.generation fine).vertices) :
    generationBlockRawGraphIsoCompletion20261011 rule coarse fine configuration
      ((rule.generation coarse).network.cellVertex (rule.generation fine).network edge point) =
      (generationBlockCellEmbedding rule coarse fine edge).vertex point := by
  rfl

theorem generation_block_weighted_distance_transport_completion20261011
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (cost : Sym2 (Fin (rule.generation (coarse + fine + 1)).vertices) → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    (first last : (rule.generation coarse).network.SubstitutionVertex (rule.generation fine).network) :
    weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph configuration) cost
      ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ first))
      ((rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ last)) =
    weightedDistance ((rule.generation coarse).network.substitutedGraph (rule.generation fine).network
      (generationBlockCells rule coarse fine configuration))
      (fun bond => cost (bond.map (fun point =>
        (rule.generationBlockDecomposition coarse fine).vertex.symm (Fintype.equivFin _ point)))) first last := by
  exact weightedDistance_graphIso (generationBlockRawGraphIsoCompletion20261011 rule coarse fine configuration)
    cost nonnegative first last

end
end IGSIII34.ResistanceLimit
