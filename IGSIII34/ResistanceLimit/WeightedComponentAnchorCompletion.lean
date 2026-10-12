import IGSIII34.ResistanceLimit.WeightedSplitAnchorCompletion

/-! Available anchors for distinct local components of one actual cell. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem weighted_cell_distinct_components_boundary_separation_completion
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (first last : Fin innerVertices)
    (firstAvailable : (inner.openGraph (configuration edge)).Reachable inner.source first ∨
      (inner.openGraph (configuration edge)).Reachable inner.target first)
    (lastAvailable : (inner.openGraph (configuration edge)).Reachable inner.source last ∨
      (inner.openGraph (configuration edge)).Reachable inner.target last)
    (disconnected : ¬ (inner.openGraph (configuration edge)).Reachable first last)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner edge first) (outer.cellVertex inner edge last)) :
    weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target first +
    weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target last ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) := by
  rcases firstAvailable with firstSource | firstTarget <;> rcases lastAvailable with lastSource | lastTarget
  · exact False.elim (disconnected (firstSource.symm.trans lastSource))
  · exact weighted_noncrossing_sides_boundary_separation_completion outer inner configuration cost
      nonnegative edge first last (fun crossed => disconnected (firstSource.symm.trans (crossed.trans lastTarget)))
      firstSource lastTarget reachable
  · have bound := weighted_noncrossing_sides_boundary_separation_completion outer inner configuration cost
      nonnegative edge last first (fun crossed => disconnected ((lastSource.symm.trans (crossed.trans firstTarget)).symm))
      lastSource firstTarget reachable.symm
    rw [weightedDistance_comm (outer.substitutedGraph inner configuration) cost nonnegative
      (outer.cellVertex inner edge last) (outer.cellVertex inner edge first)] at bound
    simpa only [add_comm] using bound
  · exact False.elim (disconnected (firstTarget.symm.trans lastTarget))

theorem weighted_cell_distinct_components_available_anchors_completion
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (first last : Fin innerVertices)
    (firstAvailable : (inner.openGraph (configuration edge)).Reachable inner.source first ∨
      (inner.openGraph (configuration edge)).Reachable inner.target first)
    (lastAvailable : (inner.openGraph (configuration edge)).Reachable inner.source last ∨
      (inner.openGraph (configuration edge)).Reachable inner.target last)
    (disconnected : ¬ (inner.openGraph (configuration edge)).Reachable first last)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner edge first) (outer.cellVertex inner edge last)) :
    ∃ firstSide lastSide : Bool,
      (inner.openGraph (configuration edge)).Reachable (plantedVertex inner firstSide) first ∧
      (inner.openGraph (configuration edge)).Reachable (plantedVertex inner lastSide) last ∧
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge (plantedVertex inner firstSide)) (outer.cellVertex inner edge first) +
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge (plantedVertex inner lastSide)) (outer.cellVertex inner edge last) ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) := by
  obtain ⟨firstSide, firstReachable, firstBound⟩ := weighted_cell_available_anchor_near outer inner configuration
    cost nonnegative edge first firstAvailable
  obtain ⟨lastSide, lastReachable, lastBound⟩ := weighted_cell_available_anchor_near outer inner configuration
    cost nonnegative edge last lastAvailable
  exact ⟨firstSide, lastSide, firstReachable, lastReachable,
    (add_le_add firstBound lastBound).trans
      (weighted_cell_distinct_components_boundary_separation_completion outer inner configuration cost
        nonnegative edge first last firstAvailable lastAvailable disconnected reachable)⟩

end
end IGSIII34.ResistanceLimit
