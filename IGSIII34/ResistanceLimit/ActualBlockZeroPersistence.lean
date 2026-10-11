import IGSIII34.ResistanceLimit.CellZeroExtension
import IGSIII.Geometry.ActualBlockCellEmbedding

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry

def actualBlockZeroExtension (rule : Rule) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (supplied : Fin (rule.generation fine).vertices → ℝ) :
    Fin (rule.generation (coarse + fine + 1)).vertices → ℝ :=
  fun vertex => cellZeroExtension (rule.generation coarse).network (rule.generation fine).network chosen supplied
    ((Fintype.equivFin _).symm ((rule.generationBlockDecomposition coarse fine).vertex vertex))

theorem actualBlockZeroExtension_old (rule : Rule) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (supplied : Fin (rule.generation fine).vertices → ℝ) (vertex : Fin (rule.generation coarse).vertices) :
    actualBlockZeroExtension rule coarse fine chosen supplied (blockOldVertexEmbedding rule coarse fine vertex) = 0 := by
  simp only [actualBlockZeroExtension, blockOldVertexEmbedding, Function.Embedding.coeFn_mk,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rfl

theorem actualBlockZeroExtension_chosen (rule : Rule) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (supplied : Fin (rule.generation fine).vertices → ℝ)
    (atSource : supplied (rule.generation fine).network.source = 0)
    (atTarget : supplied (rule.generation fine).network.target = 0)
    (vertex : Fin (rule.generation fine).vertices) :
    actualBlockZeroExtension rule coarse fine chosen supplied
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex vertex) = supplied vertex := by
  change cellZeroExtension (rule.generation coarse).network (rule.generation fine).network chosen supplied
    ((Fintype.equivFin _).symm ((rule.generationBlockDecomposition coarse fine).vertex
      ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network chosen vertex))))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact cellZeroExtension_chosen (rule.generation coarse).network (rule.generation fine).network
    chosen supplied atSource atTarget vertex

theorem actualBlockZeroExtension_other (rule : Rule) (coarse fine : ℕ)
    (chosen other : Fin (rule.generation coarse).edges) (different : other ≠ chosen)
    (supplied : Fin (rule.generation fine).vertices → ℝ) (vertex : Fin (rule.generation fine).vertices) :
    actualBlockZeroExtension rule coarse fine chosen supplied
      ((generationBlockCellEmbedding rule coarse fine other).vertex vertex) = 0 := by
  change cellZeroExtension (rule.generation coarse).network (rule.generation fine).network chosen supplied
    ((Fintype.equivFin _).symm ((rule.generationBlockDecomposition coarse fine).vertex
      ((rule.generationBlockDecomposition coarse fine).vertex.symm
        (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network other vertex))))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact cellZeroExtension_other (rule.generation coarse).network (rule.generation fine).network
    chosen other different supplied vertex

/-- Zero extensions of coherent cell potentials are coherent on the actual
global retained skeleton. All old coarse junction values are zero. -/
theorem actualBlockZeroExtension_next (rule : Rule) (coarse fine : ℕ)
    (chosen : Fin (rule.generation coarse).edges)
    (supplied : Fin (rule.generation fine).vertices → ℝ)
    (later : Fin (rule.generation (fine + 1)).vertices → ℝ)
    (atSource : supplied (rule.generation fine).network.source = 0)
    (atTarget : supplied (rule.generation fine).network.target = 0)
    (laterSource : later (rule.generation (fine + 1)).network.source = 0)
    (laterTarget : later (rule.generation (fine + 1)).network.target = 0)
    (restriction : ∀ vertex, later (rule.generationOldVertex fine vertex) = supplied vertex)
    (vertex : Fin (rule.generation (coarse + fine + 1)).vertices) :
    actualBlockZeroExtension rule coarse (fine + 1) chosen later
      (rule.generationOldVertex (coarse + fine + 1) vertex) =
      actualBlockZeroExtension rule coarse fine chosen supplied vertex := by
  classical
  let coordinates := ((Fintype.equivFin ((rule.generation coarse).network.SubstitutionVertex
    (rule.generation fine).network)).trans (rule.generationBlockDecomposition coarse fine).vertex.symm)
  obtain ⟨point, equality⟩ := coordinates.surjective vertex
  subst vertex
  cases point with
  | inl old =>
      change actualBlockZeroExtension rule coarse (fine + 1) chosen later
        (rule.generationOldVertex (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine old)) = _
      rw [blockOldVertexEmbedding_next, actualBlockZeroExtension_old]
      exact (actualBlockZeroExtension_old rule coarse fine chosen supplied old).symm
  | inr pair =>
      rcases pair with ⟨other, inside⟩
      have identity : (rule.generation coarse).network.cellVertex (rule.generation fine).network other inside.val =
          Sum.inr (other, inside) := by
        simp only [Universality.FiniteNetwork.cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
        rfl
      have valueIdentity : coordinates (Sum.inr (other, inside)) =
          (generationBlockCellEmbedding rule coarse fine other).vertex inside.val := by
        change _ = (rule.generationBlockDecomposition coarse fine).vertex.symm
          (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network other inside.val))
        rw [identity]
        rfl
      rw [valueIdentity, generationBlockCellEmbedding_next]
      by_cases same : other = chosen
      · subst other
        rw [actualBlockZeroExtension_chosen rule coarse (fine + 1) chosen later laterSource laterTarget,
          restriction, actualBlockZeroExtension_chosen rule coarse fine chosen supplied atSource atTarget]
      · rw [actualBlockZeroExtension_other rule coarse (fine + 1) chosen other same,
          actualBlockZeroExtension_other rule coarse fine chosen other same]

end
end IGSIII34.ResistanceLimit
