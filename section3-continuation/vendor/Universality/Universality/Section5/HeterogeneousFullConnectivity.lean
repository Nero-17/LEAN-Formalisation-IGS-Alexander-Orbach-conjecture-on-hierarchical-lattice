import Universality.Section5.HeterogeneousNetwork
import Universality.Graph.SubstitutionConnectivity

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

/-- Full vertex connectivity, stronger than connection of the two terminals. -/
theorem heterogeneousSubstitute_all_vertices_connected
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ edge vertex, (S edge).fullGraph.Reachable (S edge).source vertex) :
    ∀ vertex, (R.heterogeneousSubstitute S).fullGraph.Reachable (R.heterogeneousSubstitute S).source vertex := by
  intro vertex
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.HeterogeneousVertex S)).surjective vertex
  change ((R.heterogeneousSubstitute S).openGraph
      (heterogeneousConfigurationEquiv (fun (edge : Fin outerEdges) (_ : Fin (innerEdges edge)) => true))).Reachable
    (Fintype.equivFin _ (Sum.inl R.source)) (Fintype.equivFin _ vertex)
  rw [R.heterogeneousSubstitute_reachable_iff S]
  have hcoarse : heterogeneousCoarseConfiguration S
      (fun (edge : Fin outerEdges) (_ : Fin (innerEdges edge)) => true) = fun _ => true := by
    funext edge
    exact ((S edge).crosses_eq_true _).mpr (hinner edge (S edge).target)
  have houterLift (old : Fin outerVertices) :
      (R.heterogeneousSubstitutedGraph S (fun (edge : Fin outerEdges) (_ : Fin (innerEdges edge)) => true)).Reachable
        (Sum.inl R.source) (Sum.inl old) := by
    apply R.heterogeneousCoarseReachable_lifts S
    rw [hcoarse]
    exact houter old
  cases vertex with
  | inl old => exact houterLift old
  | inr pair =>
      rcases pair with ⟨edge, inside⟩
      have hcell := (hinner edge inside.val).map
        (R.heterogeneousCellHom S (fun (edge : Fin outerEdges) (_ : Fin (innerEdges edge)) => true) edge)
      change (R.heterogeneousSubstitutedGraph S _).Reachable
        (R.heterogeneousCellVertex S edge (S edge).source) (R.heterogeneousCellVertex S edge inside.val) at hcell
      rw [R.heterogeneousCellVertex_source S edge] at hcell
      have hinside : R.heterogeneousCellVertex S edge inside.val = Sum.inr ⟨edge, inside⟩ := by
        simp [heterogeneousCellVertex, inside.property.1, inside.property.2]
      rw [hinside] at hcell
      exact (houterLift (R.endpoint edge).1).trans hcell

end
end Universality.FiniteNetwork

