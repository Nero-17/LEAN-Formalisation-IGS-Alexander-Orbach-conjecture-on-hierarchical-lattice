import IGSIII34.ResistanceLimit.SourceTrace

/-! Actual finite trace minimizers preserve a flat cell. The individual-cell
identity is extracted from the nonnegative Dirichlet gaps and equality of the
whole finite trace. It is not included in the minimizer's assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

theorem finite_potential_constant_of_zero_energy
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (potential : Vertex → ℝ)
    (zero : network.potentialEnergy resistance potential = 0)
    (first last : Vertex) (reachable : network.graph.Reachable first last) :
    potential first = potential last := by
  by_cases distinct : first ≠ last
  · have distancePositive := pairResistance_pos network resistance positive distinct reachable
    have below := pairResistance_energy_lower_bound network resistance positive distinct reachable potential
    rw [zero] at below
    have multiplied := mul_le_mul_of_nonneg_right below distancePositive.le
    rw [div_mul_cancel₀ _ distancePositive.ne', zero_mul] at multiplied
    nlinarith [sq_nonneg (potential first - potential last)]
  · exact congrArg potential (not_ne_iff.mp distinct)

theorem substituted_trace_minimizer_cell_energy
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : outer.SubstitutionVertex inner → ℝ)
    (minimizing : (substitutedNetwork outer inner configuration).potentialEnergy resistance potential =
      coarsePotentialEnergy outer inner configuration resistance (fun vertex => potential (Sum.inl vertex)))
    (edge : Fin outerEdges) :
    (network inner (configuration edge)).potentialEnergy (fun child => resistance ⟨edge, child⟩)
      (fun point => potential (outer.cellVertex inner edge point)) =
      cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
        (potential (Sum.inl (outer.endpoint edge).1)) (potential (Sum.inl (outer.endpoint edge).2)) := by
  have lower (edge : Fin outerEdges) := cellTraceEnergy_le_potentialEnergy inner (configuration edge)
    (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩)
    (fun point => potential (outer.cellVertex inner edge point))
  simp only [Universality.FiniteNetwork.cellVertex_source, Universality.FiniteNetwork.cellVertex_target] at lower
  have sumZero : (∑ edge,
      ((network inner (configuration edge)).potentialEnergy (fun child => resistance ⟨edge, child⟩)
        (fun point => potential (outer.cellVertex inner edge point)) -
      cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
        (potential (Sum.inl (outer.endpoint edge).1)) (potential (Sum.inl (outer.endpoint edge).2)))) = 0 := by
    rw [Finset.sum_sub_distrib, ← substitutedNetwork_energy_sum]
    change (substitutedNetwork outer inner configuration).potentialEnergy resistance potential -
      coarsePotentialEnergy outer inner configuration resistance (fun vertex => potential (Sum.inl vertex)) = 0
    exact sub_eq_zero.mpr minimizing
  have below := Finset.single_le_sum (fun other _ => sub_nonneg.mpr (lower other)) (Finset.mem_univ edge)
  rw [sumZero] at below
  exact le_antisymm (by linarith) (lower edge)

theorem substituted_trace_minimizer_flat_cell
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : outer.SubstitutionVertex inner → ℝ)
    (minimizing : (substitutedNetwork outer inner configuration).potentialEnergy resistance potential =
      coarsePotentialEnergy outer inner configuration resistance (fun vertex => potential (Sum.inl vertex)))
    (edge : Fin outerEdges)
    (traceZero : cellTraceEnergy inner (configuration edge) (fun child => resistance ⟨edge, child⟩)
        (potential (Sum.inl (outer.endpoint edge).1)) (potential (Sum.inl (outer.endpoint edge).2)) = 0)
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    potential (outer.cellVertex inner edge first) = potential (outer.cellVertex inner edge last) := by
  have energyZero := (substituted_trace_minimizer_cell_energy outer inner configuration resistance positive potential
    minimizing edge).trans traceZero
  exact finite_potential_constant_of_zero_energy (network inner (configuration edge))
    (fun child => resistance ⟨edge, child⟩) (fun child => positive ⟨edge, child⟩)
    (fun point => potential (outer.cellVertex inner edge point)) energyZero first last (by rwa [graph_eq_openGraph])

end
end IGSIII34.ResistanceLimit
