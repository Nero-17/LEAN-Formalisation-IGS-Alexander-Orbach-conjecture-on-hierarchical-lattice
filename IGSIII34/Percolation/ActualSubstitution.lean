import IGSIII34.Percolation.SubstitutionTrace
import IGSIII34.Resistance.Reindex

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

def substitutionOpenEdgeEquiv
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges) :
    (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) ≃
      {edge : Fin (outerEdges * innerEdges) //
        Universality.FiniteNetwork.substitutionConfigurationEquiv configuration edge = true} :=
  Equiv.ofBijective (fun edge => ⟨finProdFinEquiv (edge.1, edge.2.val), by
      change configuration (finProdFinEquiv.symm (finProdFinEquiv (edge.1, edge.2.val))).1
        (finProdFinEquiv.symm (finProdFinEquiv (edge.1, edge.2.val))).2 = true
      simpa only [Equiv.symm_apply_apply] using edge.2.property⟩) (by
    constructor
    · rintro ⟨edge, child, opened⟩ ⟨otherEdge, otherChild, otherOpened⟩ equality
      have pairEquality := finProdFinEquiv.injective (congrArg Subtype.val equality)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEquality
      rfl
    · rintro ⟨edge, opened⟩
      refine ⟨⟨(finProdFinEquiv.symm edge).1, ⟨(finProdFinEquiv.symm edge).2, opened⟩⟩, ?_⟩
      exact Subtype.ext (Equiv.apply_symm_apply finProdFinEquiv edge))

theorem actual_substitution_conductance
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    (network (outer.substitute inner) (Universality.FiniteNetwork.substitutionConfigurationEquiv configuration)).effectiveConductance
        (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge)) =
      (network outer (inner.coarseConfiguration configuration)).effectiveConductance
        (coarseResistance inner configuration resistance) := by
  rw [effectiveConductance_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (Universality.FiniteNetwork.substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration) (by
      intro edge
      exact outer.substitute_endpoint inner edge.1 edge.2.val) rfl rfl]
  exact substitutedNetwork_conductance outer inner configuration resistance positive

theorem actual_substitution_crosses
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (crosses : outer.crosses (inner.coarseConfiguration configuration) = true) :
    (outer.substitute inner).crosses (Universality.FiniteNetwork.substitutionConfigurationEquiv configuration) = true := by
  apply ((outer.substitute inner).crosses_eq_true _).mpr
  exact (outer.substitute_reachable_iff inner configuration _ _).mpr
    ((outer.substitutedReachable_iff inner configuration outer.source outer.target).mpr
      ((outer.crosses_eq_true _).mp crosses))

theorem actual_substitution_resistance
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Universality.FiniteNetwork.Configuration innerEdges)
    (crosses : outer.crosses (inner.coarseConfiguration configuration) = true)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    (network (outer.substitute inner) (Universality.FiniteNetwork.substitutionConfigurationEquiv configuration)).effectiveResistance
        (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge)) =
      (network outer (inner.coarseConfiguration configuration)).effectiveResistance
        (coarseResistance inner configuration resistance) := by
  have equality := actual_substitution_conductance outer inner configuration resistance positive
  rw [effectiveConductance_eq_reciprocalResistance _
      (connected_of_crosses _ _ (actual_substitution_crosses outer inner configuration crosses))
      (fun edge => positive ((substitutionOpenEdgeEquiv configuration).symm edge)),
    effectiveConductance_eq_reciprocalResistance _ (connected_of_crosses outer _ crosses)
      (coarseResistance_positive inner configuration resistance positive)] at equality
  exact inv_injective (by simpa only [one_div] using equality)

end
end IGSIII34.Percolation
