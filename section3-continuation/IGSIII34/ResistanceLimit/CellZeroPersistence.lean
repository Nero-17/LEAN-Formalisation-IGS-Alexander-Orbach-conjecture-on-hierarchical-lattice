import IGSIII34.ResistanceLimit.CellZeroExtension
import Universality.Graph.SubstitutionAssociativity

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork

theorem cellZeroExtension_associator_old
    {outerVertices outerEdges innerVertices innerEdges nextVertices nextEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (next : Universality.FiniteNetwork nextVertices nextEdges)
    (chosen : Fin outerEdges) (supplied : Fin innerVertices → ℝ)
    (later : Fin (Fintype.card (inner.SubstitutionVertex next)) → ℝ)
    (atSource : later (inner.substitute next).source = 0)
    (atTarget : later (inner.substitute next).target = 0)
    (restriction : ∀ vertex, later (Fintype.equivFin _ (Sum.inl vertex : inner.SubstitutionVertex next)) = supplied vertex)
    (vertex : outer.SubstitutionVertex inner) :
    cellZeroExtension outer (inner.substitute next) chosen later
      ((Fintype.equivFin _).symm (outer.substitutionAssociatorVertex inner next
        (Fintype.equivFin _ (Sum.inl (Fintype.equivFin _ vertex) : (outer.substitute inner).SubstitutionVertex next)))) =
      cellZeroExtension outer inner chosen supplied vertex := by
  classical
  cases vertex with
  | inl vertex =>
      rw [outer.substitutionAssociatorVertex_old, Equiv.symm_apply_apply]
      rfl
  | inr pair =>
      rcases pair with ⟨other, inside⟩
      have identity : outer.cellVertex inner other inside.val = Sum.inr (other, inside) := by
        simp only [Universality.FiniteNetwork.cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
        rfl
      rw [← identity, outer.substitutionAssociator_coarse_cell, Equiv.symm_apply_apply]
      by_cases same : other = chosen
      · subst other
        rw [cellZeroExtension_chosen outer (inner.substitute next) chosen later atSource atTarget, restriction, identity]
        simp only [cellZeroExtension, Sum.elim_inr, ↓reduceIte]
      · rw [cellZeroExtension_other outer (inner.substitute next) chosen other same, identity]
        simp only [cellZeroExtension, Sum.elim_inr, if_neg same]

end
end IGSIII34.ResistanceLimit
