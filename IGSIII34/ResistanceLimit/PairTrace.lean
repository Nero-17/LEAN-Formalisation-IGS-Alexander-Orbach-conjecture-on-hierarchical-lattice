import IGSIII34.ResistanceLimit.PairResistance
import IGSIII34.Percolation.ActualSubstitution

/-!
# Exact trace invariance for all pairs of planted coarse vertices

The existing finite substitution theorem is applied after changing the actual
outer terminals. This proves invariance of every coarse resistance distance,
including vertices located in dangling branches of the retained component.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

def retargetOuter (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (first last : Fin outerVertices) (distinct : first ≠ last) : Universality.FiniteNetwork outerVertices outerEdges :=
  { outer with source := first, target := last, terminals_distinct := distinct }

theorem substituted_pairResistance_trace
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (first last : Fin outerVertices)
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable first last) :
    pairResistance (substitutedNetwork outer inner configuration) resistance (Sum.inl first) (Sum.inl last) =
      pairResistance (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) first last := by
  by_cases distinct : first ≠ last
  · have liftedDistinct : (Sum.inl first : outer.SubstitutionVertex inner) ≠ Sum.inl last :=
      fun equality => distinct (Sum.inl.inj equality)
    have crossing : (retargetOuter outer first last distinct).crosses (inner.coarseConfiguration configuration) = true :=
      ((retargetOuter outer first last distinct).crosses_eq_true _).mpr reachable
    simpa only [pairResistance, dif_pos distinct, dif_pos liftedDistinct, retargetOuter, retarget,
      substitutedNetwork, network, Universality.FiniteNetwork.cellVertex,
      Universality.FiniteNetwork.SubstitutionVertex] using
      substitutedNetwork_resistance (retargetOuter outer first last distinct) inner configuration crossing resistance positive
  · have equal := not_ne_iff.mp distinct
    subst last
    rw [pairResistance_self, pairResistance_self]

theorem actual_substitution_pairResistance_trace
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (first last : Fin outerVertices)
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable first last) :
    pairResistance (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge))
      (Fintype.equivFin _ (Sum.inl first : outer.SubstitutionVertex inner))
      (Fintype.equivFin _ (Sum.inl last : outer.SubstitutionVertex inner)) =
      pairResistance (network outer (inner.coarseConfiguration configuration))
        (coarseResistance inner configuration resistance) first last := by
  by_cases distinct : first ≠ last
  · have liftedDistinct : Fintype.equivFin _ (Sum.inl first : outer.SubstitutionVertex inner) ≠
        Fintype.equivFin _ (Sum.inl last : outer.SubstitutionVertex inner) :=
      fun equality => distinct (Sum.inl.inj ((Fintype.equivFin _).injective equality))
    have crossing : (retargetOuter outer first last distinct).crosses (inner.coarseConfiguration configuration) = true :=
      ((retargetOuter outer first last distinct).crosses_eq_true _).mpr reachable
    simpa only [pairResistance, dif_pos distinct, dif_pos liftedDistinct, retargetOuter, retarget,
      network, Universality.FiniteNetwork.substitute, Universality.FiniteNetwork.cellVertex,
      Universality.FiniteNetwork.SubstitutionVertex] using
      actual_substitution_resistance (retargetOuter outer first last distinct) inner configuration crossing resistance positive
  · have equal := not_ne_iff.mp distinct
    subst last
    rw [pairResistance_self, pairResistance_self]

end
end IGSIII34.ResistanceLimit
