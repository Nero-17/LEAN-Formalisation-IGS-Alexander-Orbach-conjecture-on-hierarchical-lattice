import IGSIII34.ResistanceLimit.SourceHarmonicFlatnessCompletion
import IGSIII34.ResistanceLimit.HarmonicMaximumPrincipleCompletion

/-! Maximum principles for actual source-cluster trace minimizers. Bounds are
required only at retained available terminals, so an absent B-side never
adds a fictitious zero boundary value. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

theorem source_trace_minimizer_cell_upper_bound
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
    (edge : Fin outerEdges) (bound : ℝ)
    (boundaryUpper : ∀ terminal : Fin innerVertices, terminal = inner.source ∨ terminal = inner.target →
      (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) →
      potential (outer.cellVertex inner edge terminal) ≤ bound)
    (vertex : Fin innerVertices)
    (available : (inner.openGraph (configuration edge)).Reachable inner.source vertex ∨
      (inner.openGraph (configuration edge)).Reachable inner.target vertex)
    (retained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge vertex)) :
    potential (outer.cellVertex inner edge vertex) ≤ bound := by
  have terminalRetained (terminal : Fin innerVertices)
      (reachable : (inner.openGraph (configuration edge)).Reachable terminal vertex) :
      (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) := by
    apply retained.trans
    rw [substitutedNetwork_graph_eq]
    exact (reachable.map (outer.cellHom inner configuration edge)).symm
  by_cases crossing : inner.crosses (configuration edge) = true
  · have both :
        (substitutedNetwork outer inner configuration).graph.Reachable
          (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge inner.source) ∧
        (substitutedNetwork outer inner configuration).graph.Reachable
          (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge inner.target) := by
      have localCrossing := (inner.crosses_eq_true (configuration edge)).mp crossing
      rcases available with fromSource | fromTarget
      · exact ⟨terminalRetained _ fromSource, terminalRetained _ (localCrossing.symm.trans fromSource)⟩
      · exact ⟨terminalRetained _ (localCrossing.trans fromTarget), terminalRetained _ fromTarget⟩
    have cellEnergy := substituted_trace_minimizer_cell_energy outer inner configuration resistance positive
      (sourceProjection (substitutedNetwork outer inner configuration) potential)
      (source_trace_minimizer_projected_minimal outer inner configuration resistance potential minimizing) edge
    rw [← outer.cellVertex_source inner edge, ← outer.cellVertex_target inner edge] at cellEnergy
    have upper := cell_trace_minimizer_upper_bound inner (configuration edge)
      (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩)
      (fun point => sourceProjection (substitutedNetwork outer inner configuration) potential (outer.cellVertex inner edge point))
      cellEnergy bound
      (by simpa only [sourceProjection, if_pos both.1] using boundaryUpper inner.source (Or.inl rfl) both.1)
      (by simpa only [sourceProjection, if_pos both.2] using boundaryUpper inner.target (Or.inr rfl) both.2)
      vertex available
    simpa only [sourceProjection, if_pos retained] using upper
  · rcases available with fromSource | fromTarget
    · have sourceRetained := terminalRetained inner.source fromSource
      have equal := source_trace_minimizer_flat_cell outer inner configuration resistance positive potential minimizing edge
        (fun crosses => False.elim (crossing crosses)) inner.source vertex fromSource sourceRetained retained
      exact equal.symm ▸ boundaryUpper inner.source (Or.inl rfl) sourceRetained
    · have targetRetained := terminalRetained inner.target fromTarget
      have equal := source_trace_minimizer_flat_cell outer inner configuration resistance positive potential minimizing edge
        (fun crosses => False.elim (crossing crosses)) inner.target vertex fromTarget targetRetained retained
      exact equal.symm ▸ boundaryUpper inner.target (Or.inr rfl) targetRetained

theorem sourceComponentEnergy_neg_completion
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) (potential : Vertex → ℝ) :
    sourceComponentEnergy network resistance (fun vertex => -potential vertex) =
      sourceComponentEnergy network resistance potential := by
  unfold sourceComponentEnergy finiteEnergy
  apply Finset.sum_congr rfl
  intro edge _
  congr 1
  ring

theorem source_trace_minimizer_cell_lower_bound
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
    (edge : Fin outerEdges) (bound : ℝ)
    (boundaryLower : ∀ terminal : Fin innerVertices, terminal = inner.source ∨ terminal = inner.target →
      (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) →
      bound ≤ potential (outer.cellVertex inner edge terminal))
    (vertex : Fin innerVertices)
    (available : (inner.openGraph (configuration edge)).Reachable inner.source vertex ∨
      (inner.openGraph (configuration edge)).Reachable inner.target vertex)
    (retained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge vertex)) :
    bound ≤ potential (outer.cellVertex inner edge vertex) := by
  have negativeMinimizing : sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance
      (fun vertex => -potential vertex) =
    sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
      (coarseResistance inner configuration resistance) (fun vertex => -potential (Sum.inl vertex)) := by
    rw [sourceComponentEnergy_neg_completion, sourceComponentEnergy_neg_completion]
    exact minimizing
  have upper := source_trace_minimizer_cell_upper_bound outer inner configuration resistance positive
    (fun vertex => -potential vertex) negativeMinimizing edge (-bound)
    (fun terminal boundary terminalRetained => by linarith [boundaryLower terminal boundary terminalRetained])
    vertex available retained
  linarith

theorem source_trace_minimizer_cell_deviation
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
    (edge : Fin outerEdges) (reference error : ℝ)
    (boundaryDeviation : ∀ terminal : Fin innerVertices, terminal = inner.source ∨ terminal = inner.target →
      (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge terminal) →
      |potential (outer.cellVertex inner edge terminal) - reference| ≤ error)
    (vertex : Fin innerVertices)
    (available : (inner.openGraph (configuration edge)).Reachable inner.source vertex ∨
      (inner.openGraph (configuration edge)).Reachable inner.target vertex)
    (retained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source (outer.cellVertex inner edge vertex)) :
    |potential (outer.cellVertex inner edge vertex) - reference| ≤ error := by
  have upper := source_trace_minimizer_cell_upper_bound outer inner configuration resistance positive potential minimizing
    edge (reference + error) (fun terminal boundary terminalRetained => by
      linarith [(abs_le.mp (boundaryDeviation terminal boundary terminalRetained)).2]) vertex available retained
  have lower := source_trace_minimizer_cell_lower_bound outer inner configuration resistance positive potential minimizing
    edge (reference - error) (fun terminal boundary terminalRetained => by
      linarith [(abs_le.mp (boundaryDeviation terminal boundary terminalRetained)).1]) vertex available retained
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end IGSIII34.ResistanceLimit
