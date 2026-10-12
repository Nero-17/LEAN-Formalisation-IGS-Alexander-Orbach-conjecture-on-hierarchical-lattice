import IGSIII34.ResistanceLimit.HarmonicCellFlatnessCompletion

/-! Flat-cell preservation for a source-component trace minimizer, including
noncrossing cells and hanging components. Projection discards precisely the
components absent from the actual full retained cluster. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : Universality.FiniteNetwork outerVertices outerEdges)
  (inner : Universality.FiniteNetwork innerVertices innerEdges)
  (configuration : Fin outerEdges → Configuration innerEdges)
  (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
  (positive : ∀ edge, 0 < resistance edge)
  (potential : outer.SubstitutionVertex inner → ℝ)

theorem substitution_sourceProjection_old :
    (fun vertex => sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl vertex)) =
      sourceProjection (network outer (inner.coarseConfiguration configuration)) (fun vertex => potential (Sum.inl vertex)) := by
  funext vertex
  have reachable : (substitutedNetwork outer inner configuration).graph.Reachable (Sum.inl outer.source) (Sum.inl vertex) ↔
      (network outer (inner.coarseConfiguration configuration)).graph.Reachable outer.source vertex := by
    rw [substitutedNetwork_graph_eq, graph_eq_openGraph]
    exact outer.substitutedReachable_iff inner configuration outer.source vertex
  by_cases coarseRetained : (network outer (inner.coarseConfiguration configuration)).graph.Reachable
      (network outer (inner.coarseConfiguration configuration)).source vertex
  · have fineRetained : (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (Sum.inl vertex) := reachable.mpr coarseRetained
    simp only [sourceProjection, if_pos coarseRetained, if_pos fineRetained]
  · have fineAbsent : ¬ (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (Sum.inl vertex) := fun h => coarseRetained (reachable.mp h)
    simp only [sourceProjection, if_neg coarseRetained, if_neg fineAbsent]

theorem source_trace_minimizer_projected_minimal
    (minimizing : sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance potential =
      sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex))) :
    (substitutedNetwork outer inner configuration).potentialEnergy resistance
      (sourceProjection (substitutedNetwork outer inner configuration) potential) =
      coarsePotentialEnergy outer inner configuration resistance
        (fun vertex => sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl vertex)) := by
  rw [← sourceComponentEnergy_eq_projectedEnergy, substitution_sourceProjection_old,
    coarsePotentialEnergy_eq_network_energy, ← sourceComponentEnergy_eq_projectedEnergy]
  exact minimizing

include positive in
theorem source_trace_minimizer_flat_cell
    (minimizing : sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance potential =
      sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex)))
    (edge : Fin outerEdges)
    (flatAvailable : inner.crosses (configuration edge) = true →
      sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl (outer.endpoint edge).1) =
        sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl (outer.endpoint edge).2))
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration edge)).Reachable first last)
    (firstRetained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge first))
    (lastRetained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge last)) :
    potential (outer.cellVertex inner edge first) = potential (outer.cellVertex inner edge last) := by
  have traceZero : cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
      (sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl (outer.endpoint edge).1))
      (sourceProjection (substitutedNetwork outer inner configuration) potential (Sum.inl (outer.endpoint edge).2)) = 0 := by
    by_cases crossing : inner.crosses (configuration edge) = true
    · simp only [cellTraceEnergy, crossing, if_true, flatAvailable crossing, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    · simp only [cellTraceEnergy, Bool.eq_false_iff.mpr crossing, Bool.false_eq_true, if_false]
  have equal := substituted_trace_minimizer_flat_cell outer inner configuration resistance positive
    (sourceProjection (substitutedNetwork outer inner configuration) potential)
    (source_trace_minimizer_projected_minimal outer inner configuration resistance potential minimizing) edge
    traceZero first last reachable
  simpa only [sourceProjection, if_pos firstRetained, if_pos lastRetained] using equal

end
end IGSIII34.ResistanceLimit
