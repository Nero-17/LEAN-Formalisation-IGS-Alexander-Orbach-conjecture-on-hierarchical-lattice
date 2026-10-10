import Universality.Graph.NetworkEquivalence
import Universality.Percolation.InternalVertexMass

namespace Universality
noncomputable section

def substitutionSumEquiv (α β γ δ ε : Type*) :
    ((α ⊕ (β × γ)) ⊕ ((β × δ) × ε)) ≃ (α ⊕ (β × (γ ⊕ (δ × ε)))) where
  toFun
    | .inl (.inl vertex) => .inl vertex
    | .inl (.inr (edge, vertex)) => .inr (edge, .inl vertex)
    | .inr ((edge, child), vertex) => .inr (edge, .inr (child, vertex))
  invFun
    | .inl vertex => .inl (.inl vertex)
    | .inr (edge, .inl vertex) => .inl (.inr (edge, vertex))
    | .inr (edge, .inr (child, vertex)) => .inr ((edge, child), vertex)
  left_inv x := by rcases x with (vertex | ⟨edge, vertex⟩) | ⟨⟨edge, child⟩, vertex⟩ <;> rfl
  right_inv x := by rcases x with vertex | ⟨edge, vertex | ⟨child, vertex⟩⟩ <;> rfl

namespace FiniteNetwork
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS vT eT : ℕ}
variable (R : FiniteNetwork vR eR) (S : FiniteNetwork vS eS) (T : FiniteNetwork vT eT)

def substitutionAssociatorVertex :
    Fin (Fintype.card ((R.substitute S).SubstitutionVertex T)) ≃
      Fin (Fintype.card (R.SubstitutionVertex (S.substitute T))) :=
  (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)).symm |>.trans
    (Equiv.sumCongr (Fintype.equivFin (R.SubstitutionVertex S)).symm
      (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl T.InteriorVertex))) |>.trans
    (substitutionSumEquiv (Fin vR) (Fin eR) S.InteriorVertex (Fin eS) T.InteriorVertex) |>.trans
    (Equiv.sumCongr (Equiv.refl (Fin vR))
      (Equiv.prodCongr (Equiv.refl (Fin eR)) (S.substitutionInteriorEquiv T))) |>.trans
    (Fintype.equivFin (R.SubstitutionVertex (S.substitute T)))

def substitutionAssociatorEdge : Fin ((eR * eS) * eT) ≃ Fin (eR * (eS * eT)) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin eT))) |>.trans
    (Equiv.prodAssoc (Fin eR) (Fin eS) (Fin eT)) |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin eR)) finProdFinEquiv) |>.trans finProdFinEquiv

theorem substitutionAssociatorEdge_apply (edge : Fin eR) (child : Fin eS) (leaf : Fin eT) :
    substitutionAssociatorEdge (finProdFinEquiv (finProdFinEquiv (edge, child), leaf)) =
      finProdFinEquiv (edge, finProdFinEquiv (child, leaf)) := by
  simp [substitutionAssociatorEdge]

theorem substitutionAssociatorVertex_old (vertex : Fin vR) :
    R.substitutionAssociatorVertex S T
      (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)
        (Sum.inl (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl vertex)))) =
      Fintype.equivFin (R.SubstitutionVertex (S.substitute T)) (Sum.inl vertex) := by
  simp [substitutionAssociatorVertex, substitutionSumEquiv, Equiv.sumCongr, Equiv.prodCongr]
  rfl

theorem substitutionAssociatorVertex_middle (edge : Fin eR) (vertex : S.InteriorVertex) :
    R.substitutionAssociatorVertex S T
      (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)
        (Sum.inl (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, vertex))))) =
      Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (Sum.inr (edge, S.substitutionInteriorEquiv T (Sum.inl vertex))) := by
  simp [substitutionAssociatorVertex, substitutionSumEquiv, Equiv.sumCongr, Equiv.prodCongr]
  rfl

theorem substitutionAssociatorVertex_inner (edge : Fin eR) (child : Fin eS) (vertex : T.InteriorVertex) :
    R.substitutionAssociatorVertex S T
      (Fintype.equivFin ((R.substitute S).SubstitutionVertex T)
        (Sum.inr (finProdFinEquiv (edge, child), vertex))) =
      Fintype.equivFin (R.SubstitutionVertex (S.substitute T))
        (Sum.inr (edge, S.substitutionInteriorEquiv T (Sum.inr (child, vertex)))) := by
  simp [substitutionAssociatorVertex, substitutionSumEquiv, Equiv.sumCongr, Equiv.prodCongr]
  rfl

end FiniteNetwork
end
end Universality
