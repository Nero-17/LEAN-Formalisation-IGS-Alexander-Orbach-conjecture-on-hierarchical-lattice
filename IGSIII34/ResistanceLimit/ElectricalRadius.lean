import IGSIII34.ResistanceLimit.Rayleigh
import IGSIII34.ResistanceLimit.PairTrace
import IGSIII34.ResistanceLimit.NetworkBounds
import IGSIII34.Resistance.Connectivity

/-!
# Full finite electrical component radii

The radius keeps both terminal components, with disconnected distances equal
to zero. Its one-step bound retains the intrinsic child radius and the sum of
the crossing child terminal resistances. The argument includes all dangling
interiors and treats the two sides of a noncrossing cell separately.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem pairResistance_eq_zero_of_unreachable (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) {first last : Vertex} (unreachable : ¬ network.graph.Reachable first last) :
    pairResistance network resistance first last = 0 := by
  by_cases distinct : first ≠ last
  · rw [pairResistance, dif_pos distinct]
    exact (retarget network first last distinct).disconnected_effectiveResistance unreachable resistance
  · simp [pairResistance, distinct]

theorem pairResistance_nonnegative_all (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (first last : Vertex) :
    0 ≤ pairResistance network resistance first last := by
  by_cases reachable : network.graph.Reachable first last
  · exact pairResistance_nonnegative network resistance positive reachable
  · rw [pairResistance_eq_zero_of_unreachable network resistance reachable]

def terminalResistanceRadius (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) : ℝ :=
  Finset.univ.sup' ⟨network.source, Finset.mem_univ _⟩ (fun vertex =>
    max (pairResistance network resistance network.source vertex) (pairResistance network resistance network.target vertex))

theorem sourceResistance_le_radius (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (vertex : Vertex) :
    pairResistance network resistance network.source vertex ≤ terminalResistanceRadius network resistance :=
  (le_max_left _ _).trans (Finset.le_sup' (f := fun vertex =>
    max (pairResistance network resistance network.source vertex) (pairResistance network resistance network.target vertex))
      (Finset.mem_univ vertex))

theorem targetResistance_le_radius (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (vertex : Vertex) :
    pairResistance network resistance network.target vertex ≤ terminalResistanceRadius network resistance :=
  (le_max_right _ _).trans (Finset.le_sup' (f := fun vertex =>
    max (pairResistance network resistance network.source vertex) (pairResistance network resistance network.target vertex))
      (Finset.mem_univ vertex))

theorem terminalResistanceRadius_nonnegative (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) : 0 ≤ terminalResistanceRadius network resistance := by
  have bound := sourceResistance_le_radius network resistance network.source
  rwa [pairResistance_self] at bound

theorem component_pairResistance_le_twice_radius (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (side : Bool) (first last : Vertex)
    (firstReach : network.graph.Reachable (if side then network.source else network.target) first)
    (lastReach : network.graph.Reachable (if side then network.source else network.target) last) :
    pairResistance network resistance first last ≤ 2 * terminalResistanceRadius network resistance := by
  have triangle := pairResistance_triangle network resistance positive first
    (if side then network.source else network.target) last firstReach.symm lastReach
  rw [pairResistance_comm network resistance positive firstReach.symm] at triangle
  cases side
  · simp only [Bool.false_eq_true, ↓reduceIte] at triangle
    linarith [targetResistance_le_radius network resistance first, targetResistance_le_radius network resistance last]
  · simp only [↓reduceIte] at triangle
    linarith [sourceResistance_le_radius network resistance first, sourceResistance_le_radius network resistance last]

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem substituted_child_pairResistance_le
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (edge : Fin outerEdges)
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    pairResistance (substitutedNetwork outer inner configuration) resistance
      (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) ≤
      pairResistance (network inner (configuration edge)) (fun child => resistance ⟨edge, child⟩) first last := by
  let vertices : Fin innerVertices ↪ outer.SubstitutionVertex inner :=
    ⟨outer.cellVertex inner edge, outer.cellVertex_injective inner edge⟩
  let edges : {child : Fin innerEdges // configuration edge child = true} ↪
      (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) :=
    ⟨fun child => ⟨edge, child⟩, fun first last equality => by cases equality; rfl⟩
  apply embedded_pairResistance_le (network inner (configuration edge)) (substitutedNetwork outer inner configuration)
    vertices edges (fun _ => rfl) _ _ (fun child => positive ⟨edge, child⟩) positive (fun _ => rfl)
  rwa [graph_eq_openGraph]

theorem retained_point_has_electrical_anchor
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
    (radiusBound : ∀ edge, terminalResistanceRadius (network inner (configuration edge))
      (fun child => resistance ⟨edge, child⟩) ≤ radius)
    (root : Fin outerVertices) (vertex : outer.SubstitutionVertex inner)
    (reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) vertex) :
    ∃ anchor : Fin outerVertices,
      (outer.openGraph (inner.coarseConfiguration configuration)).Reachable root anchor ∧
      pairResistance (substitutedNetwork outer inner configuration) resistance (Sum.inl anchor) vertex ≤ radius := by
  rw [outer.substitutedReachable_iff_active inner configuration root vertex] at reachable
  cases vertex with
  | inl old => exact ⟨old, reachable, by simpa [pairResistance_self] using radiusNonnegative⟩
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    change ((outer.openGraph (inner.coarseConfiguration configuration)).Reachable root (outer.endpoint edge).1 ∧
        (inner.openGraph (configuration edge)).Reachable inner.source inside.val) ∨
      ((outer.openGraph (inner.coarseConfiguration configuration)).Reachable root (outer.endpoint edge).2 ∧
        (inner.openGraph (configuration edge)).Reachable inner.target inside.val) at reachable
    have insideIdentity : outer.cellVertex inner edge inside.val = Sum.inr (edge, inside) := by
      simp only [cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
      rfl
    rcases reachable with ⟨coarseReach, childReach⟩ | ⟨coarseReach, childReach⟩
    · have comparison := substituted_child_pairResistance_le outer inner configuration resistance positive edge
        inner.source inside.val childReach
      rw [outer.cellVertex_source, insideIdentity] at comparison
      exact ⟨(outer.endpoint edge).1, coarseReach, comparison.trans
        ((sourceResistance_le_radius _ _ _).trans (radiusBound edge))⟩
    · have comparison := substituted_child_pairResistance_le outer inner configuration resistance positive edge
        inner.target inside.val childReach
      rw [outer.cellVertex_target, insideIdentity] at comparison
      exact ⟨(outer.endpoint edge).2, coarseReach, comparison.trans
        ((targetResistance_le_radius _ _ _).trans (radiusBound edge))⟩

theorem substituted_electrical_radius_bound
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (radius : ℝ) (radiusNonnegative : 0 ≤ radius)
    (radiusBound : ∀ edge, terminalResistanceRadius (network inner (configuration edge))
      (fun child => resistance ⟨edge, child⟩) ≤ radius)
    (root : Fin outerVertices) (vertex : outer.SubstitutionVertex inner)
    (reachable : (outer.substitutedGraph inner configuration).Reachable (Sum.inl root) vertex) :
    pairResistance (substitutedNetwork outer inner configuration) resistance (Sum.inl root) vertex ≤
      radius + ∑ edge, coarseResistance inner configuration resistance edge := by
  obtain ⟨anchor, coarseReach, anchorBound⟩ := retained_point_has_electrical_anchor outer inner configuration
    resistance positive radius radiusNonnegative radiusBound root vertex reachable
  have oldReach := outer.coarseReachable_lifts inner configuration coarseReach
  have triangle := pairResistance_triangle (substitutedNetwork outer inner configuration) resistance positive
    (Sum.inl root) (Sum.inl anchor) vertex (by rwa [substitutedNetwork_graph_eq])
      (by rw [substitutedNetwork_graph_eq]; exact oldReach.symm.trans reachable)
  have coarseBound := pairResistance_le_sum (network outer (inner.coarseConfiguration configuration))
    (coarseResistance inner configuration resistance) (coarseResistance_positive inner configuration resistance positive)
    root anchor (by rwa [graph_eq_openGraph])
  rw [← substituted_pairResistance_trace outer inner configuration resistance positive root anchor coarseReach] at coarseBound
  exact triangle.trans (by linarith)

end
end IGSIII34.ResistanceLimit
