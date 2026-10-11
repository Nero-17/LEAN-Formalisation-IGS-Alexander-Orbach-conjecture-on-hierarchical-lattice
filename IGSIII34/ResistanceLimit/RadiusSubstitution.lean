import IGSIII34.ResistanceLimit.PairReindex
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}


theorem substituted_terminalResistanceRadius_le
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (radius terminalBound : ℝ)
    (radiusNonnegative : 0 ≤ radius) (terminalNonnegative : 0 ≤ terminalBound)
    (radiusBound : ∀ edge, terminalResistanceRadius (network inner (configuration edge))
      (fun child => resistance ⟨edge, child⟩) ≤ radius)
    (crossingBound : ∀ edge, inner.crosses (configuration edge) = true →
      (network inner (configuration edge)).effectiveResistance (fun child => resistance ⟨edge, child⟩) ≤ terminalBound) :
    terminalResistanceRadius (substitutedNetwork outer inner configuration) resistance ≤
      radius + outerEdges * terminalBound := by
  have sumBound : (∑ edge, coarseResistance inner configuration resistance edge) ≤ outerEdges * terminalBound := by
    calc
      _ ≤ ∑ _edge : {edge : Fin outerEdges // inner.coarseConfiguration configuration edge = true}, terminalBound :=
        Finset.sum_le_sum (fun edge _ => crossingBound edge.val edge.property)
      _ ≤ ∑ _edge : Fin outerEdges, terminalBound :=
        sum_open_edges_le_sum (inner.coarseConfiguration configuration) _ (fun _ => terminalNonnegative)
      _ = _ := by simp
  have rootBound (root : Fin outerVertices) (vertex : outer.SubstitutionVertex inner) :
      pairResistance (substitutedNetwork outer inner configuration) resistance (Sum.inl root) vertex ≤
        radius + outerEdges * terminalBound := by
    by_cases reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) vertex
    · exact (substituted_electrical_radius_bound outer inner configuration resistance positive radius
        radiusNonnegative radiusBound root vertex reachable).trans (by simpa only [add_comm] using add_le_add_left sumBound radius)
    · rw [pairResistance_eq_zero_of_unreachable _ _ (by rwa [substitutedNetwork_graph_eq])]
      positivity
  apply (Finset.sup'_le_iff _ _).mpr
  intro vertex _
  exact max_le (rootBound outer.source vertex) (rootBound outer.target vertex)


end
end IGSIII34.ResistanceLimit


