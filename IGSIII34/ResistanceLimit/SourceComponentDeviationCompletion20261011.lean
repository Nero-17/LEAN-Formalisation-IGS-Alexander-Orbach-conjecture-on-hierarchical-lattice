import IGSIII34.ResistanceLimit.SourceMaximumPrincipleCompletion20261011

/-! A component-sensitive harmonic error bound. On a B socket with both
sides retained, only terminals in the point's own local component enter. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

theorem source_trace_minimizer_component_deviation
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : outer.SubstitutionVertex inner → ℝ)
    (minimizing : sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance potential =
      sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex)))
    (edge : Fin outerEdges) (reference error : ℝ) (vertex : Fin innerVertices)
    (boundaryDeviation : ∀ terminal : Fin innerVertices, terminal = inner.source ∨ terminal = inner.target →
      (inner.openGraph (configuration edge)).Reachable terminal vertex →
      (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) →
      |potential (outer.cellVertex inner edge terminal) - reference| ≤ error)
    (available : (inner.openGraph (configuration edge)).Reachable inner.source vertex ∨
      (inner.openGraph (configuration edge)).Reachable inner.target vertex)
    (retained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge vertex)) :
    |potential (outer.cellVertex inner edge vertex) - reference| ≤ error := by
  by_cases crossing : inner.crosses (configuration edge) = true
  · have localCrossing := (inner.crosses_eq_true (configuration edge)).mp crossing
    have bothAvailable : (inner.openGraph (configuration edge)).Reachable inner.source vertex ∧
        (inner.openGraph (configuration edge)).Reachable inner.target vertex := by
      rcases available with sourceAvailable | targetAvailable
      · exact ⟨sourceAvailable, localCrossing.symm.trans sourceAvailable⟩
      · exact ⟨localCrossing.trans targetAvailable, targetAvailable⟩
    apply source_trace_minimizer_cell_deviation outer inner configuration resistance positive potential minimizing
      edge reference error ?_ vertex available retained
    intro terminal boundary terminalRetained
    apply boundaryDeviation terminal boundary _ terminalRetained
    rcases boundary with rfl | rfl
    · exact bothAvailable.1
    · exact bothAvailable.2
  · have terminalRetained (terminal : Fin innerVertices)
        (reachable : (inner.openGraph (configuration edge)).Reachable terminal vertex) :
        (substitutedNetwork outer inner configuration).graph.Reachable
          (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) := by
      apply retained.trans
      rw [substitutedNetwork_graph_eq]
      exact (reachable.map (outer.cellHom inner configuration edge)).symm
    rcases available with sourceAvailable | targetAvailable
    · have sourceRetained := terminalRetained inner.source sourceAvailable
      have equal := source_trace_minimizer_flat_cell outer inner configuration resistance positive potential minimizing edge
        (fun crosses => False.elim (crossing crosses)) inner.source vertex sourceAvailable sourceRetained retained
      exact equal ▸ boundaryDeviation inner.source (Or.inl rfl) sourceAvailable sourceRetained
    · have targetRetained := terminalRetained inner.target targetAvailable
      have equal := source_trace_minimizer_flat_cell outer inner configuration resistance positive potential minimizing edge
        (fun crosses => False.elim (crossing crosses)) inner.target vertex targetAvailable targetRetained retained
      exact equal ▸ boundaryDeviation inner.target (Or.inr rfl) targetAvailable targetRetained

end
end IGSIII34.ResistanceLimit
