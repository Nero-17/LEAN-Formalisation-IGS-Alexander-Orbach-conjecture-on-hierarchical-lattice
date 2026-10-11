import IGSIII34.ResistanceLimit.SourceHarmonicFlatnessCompletion20261011
import IGSIII34.ResistanceLimit.SourceActualTrace

/-! Transfer the proved trace-minimizer flatness to the actual finite vertex
indices used by the IGS generations. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

theorem actual_substitution_source_minimizer_flat_cell
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : Fin (Fintype.card (outer.SubstitutionVertex inner)) → ℝ)
    (minimizing : sourceComponentEnergy
        (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
        (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge)) potential =
      sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance)
        (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex inner))))
    (edge : Fin outerEdges)
    (flatAvailable : inner.crosses (configuration edge) = true →
      sourceProjection (substitutedNetwork outer inner configuration)
        (fun vertex => potential (Fintype.equivFin _ vertex)) (Sum.inl (outer.endpoint edge).1) =
      sourceProjection (substitutedNetwork outer inner configuration)
        (fun vertex => potential (Fintype.equivFin _ vertex)) (Sum.inl (outer.endpoint edge).2))
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration edge)).Reachable first last)
    (firstRetained : ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (outer.substitute inner).source (Fintype.equivFin _ (outer.cellVertex inner edge first)))
    (lastRetained : ((outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (outer.substitute inner).source (Fintype.equivFin _ (outer.cellVertex inner edge last))) :
    potential (Fintype.equivFin _ (outer.cellVertex inner edge first)) =
      potential (Fintype.equivFin _ (outer.cellVertex inner edge last)) := by
  rw [sourceComponentEnergy_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration) (by
      intro leaf
      exact outer.substitute_endpoint inner leaf.1 leaf.2.val) rfl] at minimizing
  apply source_trace_minimizer_flat_cell outer inner configuration resistance positive
    (fun vertex => potential (Fintype.equivFin _ vertex)) minimizing edge flatAvailable first last reachable
  · rw [substitutedNetwork_graph_eq]
    exact (outer.substitute_reachable_iff inner configuration (Sum.inl outer.source) _).mp firstRetained
  · rw [substitutedNetwork_graph_eq]
    exact (outer.substitute_reachable_iff inner configuration (Sum.inl outer.source) _).mp lastRetained

end
end IGSIII34.ResistanceLimit
