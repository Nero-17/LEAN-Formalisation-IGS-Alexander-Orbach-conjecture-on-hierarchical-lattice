import IGSIII34.ResistanceLimit.AvailableChemicalAnchorCompletion

/-! Weighted separation of the two actual sides of a noncrossing cell.
This includes two-sided retained cells joined through the exterior graph. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

def signedWeightedComponentBoundaryDistanceCompletion
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ) (source target point : Vertex) : ℝ := by
  classical
  exact if graph.Reachable source point then weightedComponentBoundaryDistance graph cost source target point
    else -weightedComponentBoundaryDistance graph cost source target point

theorem signedWeightedComponentBoundaryDistance_adj_completion
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target : Vertex) {first last : Vertex} (adjacent : graph.Adj first last) :
    |signedWeightedComponentBoundaryDistanceCompletion graph cost source target first -
      signedWeightedComponentBoundaryDistanceCompletion graph cost source target last| ≤ cost s(first,last) := by
  have same_component := reachable_adj_iff graph adjacent source
  by_cases reached : graph.Reachable source first
  · simp only [signedWeightedComponentBoundaryDistanceCompletion, if_pos reached, if_pos (same_component.mp reached)]
    exact weightedComponentBoundaryDistance_adj graph cost nonnegative source target adjacent
  · have last_unreached : ¬ graph.Reachable source last := fun reached_last => reached (same_component.mpr reached_last)
    simp only [signedWeightedComponentBoundaryDistanceCompletion, if_neg reached, if_neg last_unreached]
    rw [show -weightedComponentBoundaryDistance graph cost source target first -
      -weightedComponentBoundaryDistance graph cost source target last =
      -(weightedComponentBoundaryDistance graph cost source target first -
        weightedComponentBoundaryDistance graph cost source target last) by ring, abs_neg]
    exact weightedComponentBoundaryDistance_adj graph cost nonnegative source target adjacent

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

def signedWeightedCellBoundaryPotentialCompletion
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) : outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun edge point =>
    signedWeightedComponentBoundaryDistanceCompletion (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target point)

theorem signedWeightedCellBoundaryPotential_cell_completion
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (point : Fin innerVertices) :
    signedWeightedCellBoundaryPotentialCompletion outer inner configuration cost (outer.cellVertex inner edge point) =
      signedWeightedComponentBoundaryDistanceCompletion (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) inner.source inner.target point := by
  apply outer.substitutionPotential_cell inner (fun _ => 0)
  · intro edge
    have zero := weightedComponentBoundaryDistance_source (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge)))
      inner.source inner.target
    simp only [signedWeightedComponentBoundaryDistanceCompletion, zero, neg_zero, ite_self]
  · intro edge
    have zero := weightedComponentBoundaryDistance_target (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge)))
      inner.source inner.target
    simp only [signedWeightedComponentBoundaryDistanceCompletion, zero, neg_zero, ite_self]

theorem signedWeightedCellBoundaryPotential_adj_completion
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    {first last : outer.SubstitutionVertex inner} (adjacent : (outer.substitutedGraph inner configuration).Adj first last) :
    |signedWeightedCellBoundaryPotentialCompletion outer inner configuration cost first -
      signedWeightedCellBoundaryPotentialCompletion outer inner configuration cost last| ≤ cost s(first,last) := by
  obtain ⟨_, edge, left, right, localAdjacent, rfl, rfl⟩ := adjacent
  rw [signedWeightedCellBoundaryPotential_cell_completion outer inner configuration cost nonnegative,
    signedWeightedCellBoundaryPotential_cell_completion outer inner configuration cost nonnegative]
  exact signedWeightedComponentBoundaryDistance_adj_completion _ _
    (fun bond => nonnegative (bond.map (outer.cellVertex inner edge))) _ _ localAdjacent

theorem weighted_noncrossing_sides_boundary_separation_completion
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (left right : Fin innerVertices)
    (noncrossing : ¬ (inner.openGraph (configuration edge)).Reachable inner.source inner.target)
    (left_reached : (inner.openGraph (configuration edge)).Reachable inner.source left)
    (right_reached : (inner.openGraph (configuration edge)).Reachable inner.target right)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner edge left) (outer.cellVertex inner edge right)) :
    weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target left +
    weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target right ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge left) (outer.cellVertex inner edge right) := by
  have right_not_source : ¬ (inner.openGraph (configuration edge)).Reachable inner.source right :=
    fun source_reached => noncrossing (source_reached.trans right_reached.symm)
  have bound := weighted_potential_distance_bound (outer.substitutedGraph inner configuration) cost
    (signedWeightedCellBoundaryPotentialCompletion outer inner configuration cost)
    (signedWeightedCellBoundaryPotential_adj_completion outer inner configuration cost nonnegative) reachable
  rw [signedWeightedCellBoundaryPotential_cell_completion outer inner configuration cost nonnegative,
    signedWeightedCellBoundaryPotential_cell_completion outer inner configuration cost nonnegative] at bound
  simpa only [signedWeightedComponentBoundaryDistanceCompletion, if_pos left_reached, if_neg right_not_source,
    sub_neg_eq_add, abs_of_nonneg (add_nonneg
      (weightedComponentBoundaryDistance_nonneg (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge))) _ _ _)
      (weightedComponentBoundaryDistance_nonneg (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge))) _ _ _))] using bound

end
end IGSIII34.ResistanceLimit
