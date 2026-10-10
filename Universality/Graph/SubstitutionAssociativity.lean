import Universality.Graph.SubstitutionAssociator
import Universality.Graph.InternalCellConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS vT eT : ℕ}
variable (R : FiniteNetwork vR eR) (S : FiniteNetwork vS eS) (T : FiniteNetwork vT eT)

theorem substitutionAssociator_coarse_cell (edge : Fin eR) (vertex : Fin vS) :
    R.substitutionAssociatorVertex S T
      (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)
        (Sum.inl (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge vertex)))) =
      Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (R.cellVertex (S.substitute T) edge
          (Fintype.equivFin (S.SubstitutionVertex T) (Sum.inl vertex))) := by
  by_cases hs : vertex = S.source
  · subst vertex
    rw [R.cellVertex_source, R.substitutionAssociatorVertex_old]
    change _ = Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
      (R.cellVertex (S.substitute T) edge (S.substitute T).source)
    rw [R.cellVertex_source]
  · by_cases ht : vertex = S.target
    · subst vertex
      rw [R.cellVertex_target, R.substitutionAssociatorVertex_old]
      change _ = Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (R.cellVertex (S.substitute T) edge (S.substitute T).target)
      rw [R.cellVertex_target]
    · have hcell : R.cellVertex S edge vertex = Sum.inr (edge, ⟨vertex, hs, ht⟩) := by
        simp only [cellVertex, dif_neg hs, dif_neg ht]
      rw [hcell, R.substitutionAssociatorVertex_middle]
      change _ = Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (R.cellVertex (S.substitute T) edge (S.substitutionInteriorEquiv T (Sum.inl ⟨vertex, hs, ht⟩)).val)
      rw [R.cellVertex_eq_interior]

theorem substitutionAssociator_cell (edge : Fin eR) (child : Fin eS) (vertex : Fin vT) :
    R.substitutionAssociatorVertex S T
      (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)
        ((R.substitute S).cellVertex T (finProdFinEquiv (edge, child)) vertex)) =
      Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (R.cellVertex (S.substitute T) edge
          (Fintype.equivFin (S.SubstitutionVertex T) (S.cellVertex T child vertex))) := by
  by_cases hs : vertex = T.source
  · subst vertex
    rw [(R.substitute S).cellVertex_source, S.cellVertex_source, R.substitute_endpoint]
    exact R.substitutionAssociator_coarse_cell S T edge (S.endpoint child).1
  · by_cases ht : vertex = T.target
    · subst vertex
      rw [(R.substitute S).cellVertex_target, S.cellVertex_target, R.substitute_endpoint]
      exact R.substitutionAssociator_coarse_cell S T edge (S.endpoint child).2
    · have hleft : (R.substitute S).cellVertex T (finProdFinEquiv (edge, child)) vertex =
          Sum.inr (finProdFinEquiv (edge, child), ⟨vertex, hs, ht⟩) := by
        simp only [cellVertex, dif_neg hs, dif_neg ht]
      have hright : S.cellVertex T child vertex = Sum.inr (child, ⟨vertex, hs, ht⟩) := by
        simp only [cellVertex, dif_neg hs, dif_neg ht]
      rw [hleft, hright, R.substitutionAssociatorVertex_inner]
      change _ = Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (R.cellVertex (S.substitute T) edge
          (S.substitutionInteriorEquiv T (Sum.inr (child, ⟨vertex, hs, ht⟩))).val)
      rw [R.cellVertex_eq_interior]

/-- Associativity is an explicit equivalence of the actual indexed networks,
including their two fixed terminals. It is not a definitional equality. -/
def substitutionAssociativity :
    ((R.substitute S).substitute T).NetworkEquivalence (R.substitute (S.substitute T)) where
  vertex := R.substitutionAssociatorVertex S T
  edge := substitutionAssociatorEdge
  source := R.substitutionAssociatorVertex_old S T R.source
  target := R.substitutionAssociatorVertex_old S T R.target
  endpoint e := by
    obtain ⟨⟨pair, leaf⟩, rfl⟩ := finProdFinEquiv.surjective e
    obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective pair
    rw [substitutionAssociatorEdge_apply, R.substitute_endpoint, S.substitute_endpoint,
      (R.substitute S).substitute_endpoint]
    apply Prod.ext
    · exact (R.substitutionAssociator_cell S T edge child (T.endpoint leaf).1).symm
    · exact (R.substitutionAssociator_cell S T edge child (T.endpoint leaf).2).symm

end
end Universality.FiniteNetwork
