import IGSIII34.ResistanceLimit.SourceEnergy
import IGSIII34.Percolation.SubstitutionTrace

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
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
    by_cases retained : (network outer (inner.coarseConfiguration configuration)).graph.Reachable
        (network outer (inner.coarseConfiguration configuration)).source vertex
    · have fine : (substitutedNetwork outer inner configuration).graph.Reachable
          (substitutedNetwork outer inner configuration).source (Sum.inl vertex) :=
        (reachability vertex).mpr retained
      simp only [sourceProjection, if_pos retained, if_pos fine]
    · have fine : ¬ (substitutedNetwork outer inner configuration).graph.Reachable
          (substitutedNetwork outer inner configuration).source (Sum.inl vertex) :=
        fun fine => retained ((reachability vertex).mp fine)
      simp only [sourceProjection, if_neg retained, if_neg fine]
  have bound := coarsePotentialEnergy_le_substituted_energy outer inner configuration resistance positive
    (sourceProjection (substitutedNetwork outer inner configuration) potential)
  rw [coarsePotentialEnergy_eq_network_energy, projectionIdentity,
    ← sourceComponentEnergy_eq_projectedEnergy,
    ← sourceComponentEnergy_eq_projectedEnergy] at bound
  exact bound

/-- The source-component trace has an attaining extension. Boundary values on
every retained old vertex are prescribed, including old vertices in branches. -/
theorem exists_sourceComponentEnergy_minimizer
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (boundary : Fin outerVertices → ℝ) :
    ∃ potential : outer.SubstitutionVertex inner → ℝ,
      (∀ vertex, (network outer (inner.coarseConfiguration configuration)).graph.Reachable outer.source vertex →
        potential (Sum.inl vertex) = boundary vertex) ∧
      sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance potential =
        sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
          (coarseResistance inner configuration resistance) boundary := by
  classical
  obtain ⟨potential, restriction, minimizing⟩ := exists_substituted_energy_minimizer outer inner configuration
    resistance positive (sourceProjection (network outer (inner.coarseConfiguration configuration)) boundary)
  rw [coarsePotentialEnergy_eq_network_energy, ← sourceComponentEnergy_eq_projectedEnergy] at minimizing
  refine ⟨potential, ?_, ?_⟩
  · intro vertex retained
    have retained' : (network outer (inner.coarseConfiguration configuration)).graph.Reachable
        (network outer (inner.coarseConfiguration configuration)).source vertex := retained
    simpa only [sourceProjection, if_pos retained'] using restriction vertex
  · have restrictionIdentity : (fun vertex => potential (Sum.inl vertex)) =
        sourceProjection (network outer (inner.coarseConfiguration configuration)) boundary := funext restriction
    have lower := sourceComponentEnergy_le_substituted_energy outer inner configuration resistance positive potential
    rw [restrictionIdentity, sourceComponentEnergy_eq_projectedEnergy] at lower
    have projectionTwice : sourceProjection (network outer (inner.coarseConfiguration configuration))
        (sourceProjection (network outer (inner.coarseConfiguration configuration)) boundary) =
        sourceProjection (network outer (inner.coarseConfiguration configuration)) boundary := by
      funext vertex
      unfold sourceProjection
      split_ifs <;> rfl
    rw [projectionTwice, ← sourceComponentEnergy_eq_projectedEnergy] at lower
    exact le_antisymm ((sourceComponentEnergy_le_potentialEnergy _ resistance positive potential).trans minimizing.le) lower

end
end IGSIII34.ResistanceLimit
