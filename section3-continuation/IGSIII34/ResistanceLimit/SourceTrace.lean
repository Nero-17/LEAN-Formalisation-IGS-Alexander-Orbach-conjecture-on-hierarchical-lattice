import IGSIII34.ResistanceLimit.SourceEnergy
import IGSIII34.Percolation.SubstitutionTrace

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Exact source-component restriction of the finite Dirichlet inequality.
The fine energy retains every dangling edge in that component. -/
theorem sourceComponentEnergy_le_substituted_energy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : outer.SubstitutionVertex inner → ℝ) :
    sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
      (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex)) ≤
    sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance potential := by
  classical
  have reachability (vertex : Fin outerVertices) :
      (substitutedNetwork outer inner configuration).graph.Reachable (Sum.inl outer.source) (Sum.inl vertex) ↔
        (network outer (inner.coarseConfiguration configuration)).graph.Reachable outer.source vertex := by
    rw [substitutedNetwork_graph_eq, graph_eq_openGraph]
    exact outer.substitutedReachable_iff inner configuration outer.source vertex
  have projectionIdentity :
      (fun vertex => sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl vertex)) =
      sourceProjection (network outer (inner.coarseConfiguration configuration)) (fun vertex => potential (Sum.inl vertex)) := by
    funext vertex
    change (if (substitutedNetwork outer inner configuration).graph.Reachable (Sum.inl outer.source) (Sum.inl vertex)
      then potential (Sum.inl vertex) else 0) =
      if (network outer (inner.coarseConfiguration configuration)).graph.Reachable outer.source vertex
      then potential (Sum.inl vertex) else 0
    rw [reachability vertex]
  have bound := coarsePotentialEnergy_le_substituted_energy outer inner configuration resistance positive
    (sourceProjection (substitutedNetwork outer inner configuration) potential)
  rw [coarsePotentialEnergy_eq_network_energy, projectionIdentity,
    ← sourceComponentEnergy_eq_projectedEnergy,
    ← sourceComponentEnergy_eq_projectedEnergy] at bound
  exact bound

end
end IGSIII34.ResistanceLimit
