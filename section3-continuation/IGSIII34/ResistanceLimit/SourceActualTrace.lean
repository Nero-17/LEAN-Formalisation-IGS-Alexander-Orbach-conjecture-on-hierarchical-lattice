import IGSIII34.ResistanceLimit.SourceTrace
import IGSIII34.ResistanceLimit.SourceReindex
import IGSIII34.Percolation.ActualSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem sourceComponentEnergy_le_actual_substitution_energy
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (potential : Fin (Fintype.card (outer.SubstitutionVertex inner)) → ℝ) :
    sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
      (coarseResistance inner configuration resistance)
      (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex inner))) ≤
    sourceComponentEnergy (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge)) potential := by
  rw [sourceComponentEnergy_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration) (by
      intro edge
      exact outer.substitute_endpoint inner edge.1 edge.2.val) rfl]
  exact sourceComponentEnergy_le_substituted_energy outer inner configuration resistance positive
    (fun vertex => potential (Fintype.equivFin _ vertex))

theorem exists_actual_sourceComponentEnergy_minimizer
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (boundary : Fin outerVertices → ℝ) :
    ∃ potential : Fin (Fintype.card (outer.SubstitutionVertex inner)) → ℝ,
      (∀ vertex, (network outer (inner.coarseConfiguration configuration)).graph.Reachable outer.source vertex →
        potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex inner)) = boundary vertex) ∧
      sourceComponentEnergy (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
        (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge)) potential =
      sourceComponentEnergy (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) boundary := by
  obtain ⟨potential, restriction, minimizing⟩ := exists_sourceComponentEnergy_minimizer
    outer inner configuration resistance positive boundary
  refine ⟨fun vertex => potential ((Fintype.equivFin _).symm vertex), ?_, ?_⟩
  · intro vertex retained
    simp only [Equiv.symm_apply_apply]
    exact restriction vertex retained
  · rw [sourceComponentEnergy_reindex (substitutedNetwork outer inner configuration)
      (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration) (by
        intro edge
        exact outer.substitute_endpoint inner edge.1 edge.2.val) rfl]
    simpa only [Equiv.symm_apply_apply] using minimizing

end
end IGSIII34.ResistanceLimit
