import IGSIII34.ResistanceLimit.CellResistanceLocalisation
import IGSIII34.ResistanceLimit.DanglingCellIsometry
import IGSIII34.ResistanceLimit.PairReindex
import IGSIII34.Percolation.ActualSubstitution

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem actual_substituted_cell_resistance_lower_bound
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges)
    (crossing : inner.crosses (configuration chosen) = true)
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration chosen)).Reachable first last) :
    pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last ≤
      (1 + cellBoundaryTestEnergy outer inner configuration resistance chosen *
        (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩)) *
      pairResistance (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
        (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge))
        (Fintype.equivFin _ (outer.cellVertex inner chosen first))
        (Fintype.equivFin _ (outer.cellVertex inner chosen last)) := by
  rw [pairResistance_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration)
    (fun edge => outer.substitute_endpoint inner edge.1 edge.2.val) resistance positive]
  exact substituted_cell_resistance_lower_bound outer inner configuration resistance positive chosen crossing first last reachable

theorem actual_substituted_dangling_cell_pairResistance_eq
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges)
    (noncrossing : inner.crosses (configuration chosen) = false) (sourceSide : Bool)
    (first last : Fin innerVertices)
    (firstRetained : (network inner (configuration chosen)).graph.Reachable
      (sideNetwork (network inner (configuration chosen)) sourceSide).source first)
    (lastRetained : (network inner (configuration chosen)).graph.Reachable
      (sideNetwork (network inner (configuration chosen)) sourceSide).source last) :
    pairResistance (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge))
      (Fintype.equivFin _ (outer.cellVertex inner chosen first))
      (Fintype.equivFin _ (outer.cellVertex inner chosen last)) =
    pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last := by
  rw [pairResistance_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration)
    (fun edge => outer.substitute_endpoint inner edge.1 edge.2.val) resistance positive]
  exact substituted_dangling_cell_pairResistance_eq outer inner configuration resistance positive chosen noncrossing sourceSide
    first last firstRetained lastRetained

end
end IGSIII34.ResistanceLimit
