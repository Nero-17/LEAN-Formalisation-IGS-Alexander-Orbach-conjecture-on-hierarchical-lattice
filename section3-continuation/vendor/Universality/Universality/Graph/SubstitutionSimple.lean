import Universality.Graph.InternalCellConnectivity
import Universality.Graph.SubstitutionDistance

namespace Universality.FiniteNetwork
noncomputable section
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem edge_has_interior_endpoint
    (hscale : 1 < S.fullGraph.dist S.source S.target) (edge : Fin innerEdges) :
    ((S.endpoint edge).1 ≠ S.source ∧ (S.endpoint edge).1 ≠ S.target) ∨
      ((S.endpoint edge).2 ≠ S.source ∧ (S.endpoint edge).2 ≠ S.target) := by
  have hnonadj : ¬ S.fullGraph.Adj S.source S.target := by
    intro hadj
    have := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    omega
  by_contra h
  push_neg at h
  have hfirst : (S.endpoint edge).1 = S.source ∨ (S.endpoint edge).1 = S.target := by tauto
  have hsecond : (S.endpoint edge).2 = S.source ∨ (S.endpoint edge).2 = S.target := by tauto
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact S.loopless edge (hfirst.trans hsecond.symm)
  · exact hnonadj ⟨S.terminals_distinct, edge, rfl, Or.inl (Prod.ext hfirst hsecond)⟩
  · exact hnonadj ⟨S.terminals_distinct, edge, rfl, Or.inr (Prod.ext hfirst hsecond)⟩
  · exact S.loopless edge (hfirst.trans hsecond.symm)

theorem cellVertex_eq_forces_same_cell {edge other : Fin outerEdges}
    {inside vertex : Fin innerVertices} (hs : inside ≠ S.source) (ht : inside ≠ S.target)
    (heq : R.cellVertex S edge inside = R.cellVertex S other vertex) : edge = other := by
  have hinside := R.cellVertex_eq_interior S edge ⟨inside, hs, ht⟩
  rw [hinside] at heq
  exact ((R.cellVertex_eq_interior_iff S other edge vertex ⟨inside, hs, ht⟩).mp heq.symm).1.symm

/-- Scale greater than one prevents an edge from lying entirely on the two
gluing vertices. Thus distinct child cells cannot produce a repeated edge. -/
theorem substitute_simple
    (hsimple : Function.Injective (fun edge => s((S.endpoint edge).1, (S.endpoint edge).2)))
    (hscale : 1 < S.fullGraph.dist S.source S.target) :
    Function.Injective (fun edge => s(((R.substitute S).endpoint edge).1,
      ((R.substitute S).endpoint edge).2)) := by
  intro first second heq
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective first
  obtain ⟨⟨other, bond⟩, rfl⟩ := finProdFinEquiv.surjective second
  simp only [substitute_endpoint] at heq
  rcases Sym2.eq_iff.mp heq with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · have hfirst := (Fintype.equivFin _).injective hfirst
    have hsecond := (Fintype.equivFin _).injective hsecond
    have hedge : edge = other := by
      rcases S.edge_has_interior_endpoint hscale child with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact R.cellVertex_eq_forces_same_cell S hs ht hfirst
      · exact R.cellVertex_eq_forces_same_cell S hs ht hsecond
    subst other
    have hchild := hsimple (Sym2.eq_iff.mpr (Or.inl
      ⟨R.cellVertex_injective S edge hfirst, R.cellVertex_injective S edge hsecond⟩))
    rw [hchild]
  · have hfirst := (Fintype.equivFin _).injective hfirst
    have hsecond := (Fintype.equivFin _).injective hsecond
    have hedge : edge = other := by
      rcases S.edge_has_interior_endpoint hscale child with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact R.cellVertex_eq_forces_same_cell S hs ht hfirst
      · exact R.cellVertex_eq_forces_same_cell S hs ht hsecond
    subst other
    have hchild := hsimple (Sym2.eq_iff.mpr (Or.inr
      ⟨R.cellVertex_injective S edge hfirst, R.cellVertex_injective S edge hsecond⟩))
    rw [hchild]

end
end Universality.FiniteNetwork
