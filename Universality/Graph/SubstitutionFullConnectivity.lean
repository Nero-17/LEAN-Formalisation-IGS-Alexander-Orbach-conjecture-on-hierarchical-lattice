import Universality.Graph.SubstitutionConnectivity

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Full vertex connectivity, stronger than connection of the two terminals. -/
theorem substitute_all_vertices_connected
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex) :
    ∀ vertex, (R.substitute S).fullGraph.Reachable (R.substitute S).source vertex := by
  intro vertex
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
  change ((R.substitute S).openGraph
      (substitutionConfigurationEquiv (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true))).Reachable
    (Fintype.equivFin _ (Sum.inl R.source)) (Fintype.equivFin _ vertex)
  rw [R.substitute_reachable_iff S]
  have hcoarse : S.coarseConfiguration
      (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true) = fun _ => true := by
    funext edge
    exact (S.crosses_eq_true _).mpr (hinner S.target)
  have houterLift (old : Fin outerVertices) :
      (R.substitutedGraph S (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true)).Reachable
        (Sum.inl R.source) (Sum.inl old) := by
    apply R.coarseReachable_lifts S
    rw [hcoarse]
    exact houter old
  cases vertex with
  | inl old => exact houterLift old
  | inr pair =>
      rcases pair with ⟨edge, inside⟩
      have hcell := (hinner inside.val).map
        (R.cellHom S (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true) edge)
      change (R.substitutedGraph S _).Reachable
        (R.cellVertex S edge S.source) (R.cellVertex S edge inside.val) at hcell
      rw [R.cellVertex_source S edge] at hcell
      have hinside : R.cellVertex S edge inside.val = Sum.inr (edge, inside) := by
        simp [cellVertex, inside.property.1, inside.property.2]
      rw [hinside] at hcell
      exact (houterLift (R.endpoint edge).1).trans hcell

end
end Universality.FiniteNetwork
