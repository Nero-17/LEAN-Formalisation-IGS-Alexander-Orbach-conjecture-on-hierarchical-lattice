import Universality.Percolation.MassEquivalence
import Universality.Graph.InternalCellConnectivity

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS vR' eR' vS' eS' : ℕ}
variable {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable {R' : FiniteNetwork vR' eR'} {S' : FiniteNetwork vS' eS'}
variable (outer : R.NetworkEquivalence R') (inner : S.NetworkEquivalence S')

def substituteVertex :
    Fin (Fintype.card (R.SubstitutionVertex S)) ≃ Fin (Fintype.card (R'.SubstitutionVertex S')) :=
  (Fintype.equivFin (R.SubstitutionVertex S)).symm |>.trans
    (Equiv.sumCongr outer.vertex (Equiv.prodCongr outer.edge inner.interior)) |>.trans
    (Fintype.equivFin (R'.SubstitutionVertex S'))

def substituteEdge : Fin (eR * eS) ≃ Fin (eR' * eS') :=
  finProdFinEquiv.symm |>.trans (Equiv.prodCongr outer.edge inner.edge) |>.trans finProdFinEquiv

theorem substituteVertex_old (vertex : Fin vR) :
    outer.substituteVertex inner (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl vertex)) =
      Fintype.equivFin (R'.SubstitutionVertex S') (Sum.inl (outer.vertex vertex)) := by
  simp [substituteVertex, Equiv.sumCongr, Equiv.prodCongr]
  rfl

theorem substituteVertex_internal (edge : Fin eR) (vertex : S.InteriorVertex) :
    outer.substituteVertex inner (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, vertex))) =
      Fintype.equivFin (R'.SubstitutionVertex S') (Sum.inr (outer.edge edge, inner.interior vertex)) := by
  simp [substituteVertex, Equiv.sumCongr, Equiv.prodCongr]
  rfl

theorem substituteVertex_cell (edge : Fin eR) (vertex : Fin vS) :
    outer.substituteVertex inner (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge vertex)) =
      Fintype.equivFin (R'.SubstitutionVertex S')
        (R'.cellVertex S' (outer.edge edge) (inner.vertex vertex)) := by
  by_cases hs : vertex = S.source
  · subst vertex
    rw [inner.source, R.cellVertex_source, R'.cellVertex_source, outer.substituteVertex_old, outer.endpoint]
  · by_cases ht : vertex = S.target
    · subst vertex
      rw [inner.target, R.cellVertex_target, R'.cellVertex_target, outer.substituteVertex_old, outer.endpoint]
    · have hcell : R.cellVertex S edge vertex = Sum.inr (edge, ⟨vertex, hs, ht⟩) := by
        simp only [cellVertex, dif_neg hs, dif_neg ht]
      rw [hcell, outer.substituteVertex_internal]
      change _ = Fintype.equivFin (R'.SubstitutionVertex S')
        (R'.cellVertex S' (outer.edge edge) (inner.interior ⟨vertex, hs, ht⟩).val)
      rw [R'.cellVertex_eq_interior]

def substitute : (R.substitute S).NetworkEquivalence (R'.substitute S') where
  vertex := outer.substituteVertex inner
  edge := outer.substituteEdge inner
  source := by
    change outer.substituteVertex inner (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source)) = _
    rw [outer.substituteVertex_old, outer.source]
    rfl
  target := by
    change outer.substituteVertex inner (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) = _
    rw [outer.substituteVertex_old, outer.target]
    rfl
  endpoint e := by
    obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective e
    have he : outer.substituteEdge inner (finProdFinEquiv (edge, child)) =
        finProdFinEquiv (outer.edge edge, inner.edge child) := by simp [substituteEdge]
    rw [he, R'.substitute_endpoint, R.substitute_endpoint, inner.endpoint]
    apply Prod.ext
    · exact (outer.substituteVertex_cell inner edge (S.endpoint child).1).symm
    · exact (outer.substituteVertex_cell inner edge (S.endpoint child).2).symm

end
end Universality.FiniteNetwork.NetworkEquivalence
