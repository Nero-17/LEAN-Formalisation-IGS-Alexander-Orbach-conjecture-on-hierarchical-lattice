import Universality.Graph.SubstitutionSymmetry

namespace Universality.FiniteNetwork.NetworkSymmetry
noncomputable section
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable {R : FiniteNetwork outerVertices outerEdges} {S : FiniteNetwork innerVertices innerEdges}

theorem edge_involutive (symmetry : R.NetworkSymmetry)
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hinvolutive : Function.Involutive symmetry.vertex) : Function.Involutive symmetry.edge := by
  intro edge
  apply hsimple
  change s((R.endpoint (symmetry.edge (symmetry.edge edge))).1,
    (R.endpoint (symmetry.edge (symmetry.edge edge))).2) = s((R.endpoint edge).1, (R.endpoint edge).2)
  have hdouble (vertex : Fin outerVertices) : symmetry.vertex (symmetry.vertex vertex) = vertex := hinvolutive vertex
  rcases symmetry.endpoint edge with hfirst | hfirst <;>
    rcases symmetry.endpoint (symmetry.edge edge) with hsecond | hsecond <;>
    simp only [hfirst, hdouble] at hsecond <;>
    rw [hsecond] <;> simp [Sym2.eq_swap]

theorem respectsOrientation_twice (symmetry : R.NetworkSymmetry)
    (hinvolutive : Function.Involutive symmetry.vertex)
    (hedge : Function.Involutive symmetry.edge) (edge : Fin outerEdges) :
    symmetry.respectsOrientation (symmetry.edge edge) ↔ symmetry.respectsOrientation edge := by
  unfold respectsOrientation
  rw [hedge edge]
  have hdouble (vertex : Fin outerVertices) : symmetry.vertex (symmetry.vertex vertex) = vertex := hinvolutive vertex
  constructor
  · intro heq
    apply Prod.ext
    · have h := congrArg (fun pair => symmetry.vertex pair.1) heq
      simpa only [hdouble] using h.symm
    · have h := congrArg (fun pair => symmetry.vertex pair.2) heq
      simpa only [hdouble] using h.symm
  · intro heq
    rw [heq]
    simp only [hdouble, Prod.eta]

theorem substitute_vertex_involutive (outerSymmetry : R.NetworkSymmetry)
    (innerSymmetry : S.NetworkSymmetry)
    (hs : innerSymmetry.vertex S.source = S.target)
    (ht : innerSymmetry.vertex S.target = S.source)
    (houter : Function.Involutive outerSymmetry.vertex)
    (hinner : Function.Involutive innerSymmetry.vertex)
    (hedge : Function.Involutive outerSymmetry.edge) :
    Function.Involutive (outerSymmetry.substitute innerSymmetry hs ht).vertex := by
  have hvertex : Function.Involutive
      (outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht) := by
    intro vertex
    cases vertex with
    | inl vertex => exact congrArg Sum.inl (houter vertex)
    | inr pair =>
      rcases pair with ⟨edge, vertex⟩
      change Sum.inr (outerSymmetry.edge (outerSymmetry.edge edge),
        outerSymmetry.orientedInterior innerSymmetry hs ht (outerSymmetry.edge edge)
          (outerSymmetry.orientedInterior innerSymmetry hs ht edge vertex)) = Sum.inr (edge, vertex)
      rw [hedge edge]
      apply congrArg Sum.inr
      apply congrArg (Prod.mk edge)
      unfold orientedInterior
      simp only [outerSymmetry.respectsOrientation_twice houter hedge edge]
      split
      · rfl
      · apply Subtype.ext
        exact hinner vertex.val
  intro vertex
  change Fintype.equivFin _
    (outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht
      ((Fintype.equivFin _).symm (Fintype.equivFin _
        (outerSymmetry.substitutionVertexEquiv innerSymmetry hs ht
          ((Fintype.equivFin _).symm vertex))))) = vertex
  rw [Equiv.symm_apply_apply, hvertex, Equiv.apply_symm_apply]

end
end Universality.FiniteNetwork.NetworkSymmetry
