import IGSIII.Geometry.CellLocalisationWeighted
import IGSIII.Geometry.CellLocalisationSplitSeparation

/-! The chemical boundary radius is attained at a genuinely available
terminal, and its actual ambient distance is no larger. These finite weighted
graph facts are the anchor step of the carrier comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry

theorem weighted_component_boundary_attained
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ) (source target point : Vertex)
    (available : graph.Reachable source point ∨ graph.Reachable target point) :
    ∃ side : Bool, graph.Reachable (if side then source else target) point ∧
      weightedDistance graph cost (if side then source else target) point =
        weightedComponentBoundaryDistance graph cost source target point := by
  classical
  by_cases fromSource : graph.Reachable source point
  · by_cases fromTarget : graph.Reachable target point
    · by_cases firstSmaller : weightedDistance graph cost source point ≤ weightedDistance graph cost target point
      · refine ⟨true, fromSource, ?_⟩
        simp only [Bool.true_eq, ↓reduceIte, weightedComponentBoundaryDistance,
          if_pos fromSource, if_pos fromTarget, min_eq_left firstSmaller]
      · refine ⟨false, fromTarget, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte, weightedComponentBoundaryDistance,
          if_pos fromSource, if_pos fromTarget, min_eq_right (le_of_not_ge firstSmaller)]
    · refine ⟨true, fromSource, ?_⟩
      simp only [Bool.true_eq, ↓reduceIte, weightedComponentBoundaryDistance, if_pos fromSource, if_neg fromTarget]
  · have fromTarget : graph.Reachable target point := available.resolve_left fromSource
    refine ⟨false, fromTarget, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, weightedComponentBoundaryDistance, if_neg fromSource, if_pos fromTarget]

theorem weighted_cell_available_anchor_near
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (point : Fin innerVertices)
    (available : (inner.openGraph (configuration edge)).Reachable inner.source point ∨
      (inner.openGraph (configuration edge)).Reachable inner.target point) :
    ∃ side : Bool,
      (inner.openGraph (configuration edge)).Reachable (plantedVertex inner side) point ∧
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge (plantedVertex inner side)) (outer.cellVertex inner edge point) ≤
      weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) inner.source inner.target point := by
  obtain ⟨side, reachable, attained⟩ := weighted_component_boundary_attained (inner.openGraph (configuration edge))
    (cellBondCost outer inner cost edge) inner.source inner.target point available
  refine ⟨side, reachable, ?_⟩
  exact (weighted_cell_distance_le outer inner configuration cost nonnegative edge reachable).trans_eq attained

theorem weighted_distinct_cells_available_anchors
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (firstEdge lastEdge : Fin outerEdges) (distinct : firstEdge ≠ lastEdge)
    (first last : Fin innerVertices)
    (firstAvailable : (inner.openGraph (configuration firstEdge)).Reachable inner.source first ∨
      (inner.openGraph (configuration firstEdge)).Reachable inner.target first)
    (lastAvailable : (inner.openGraph (configuration lastEdge)).Reachable inner.source last ∨
      (inner.openGraph (configuration lastEdge)).Reachable inner.target last)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner firstEdge first) (outer.cellVertex inner lastEdge last)) :
    ∃ firstSide lastSide : Bool,
      (inner.openGraph (configuration firstEdge)).Reachable (plantedVertex inner firstSide) first ∧
      (inner.openGraph (configuration lastEdge)).Reachable (plantedVertex inner lastSide) last ∧
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner firstEdge (plantedVertex inner firstSide)) (outer.cellVertex inner firstEdge first) +
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner lastEdge (plantedVertex inner lastSide)) (outer.cellVertex inner lastEdge last) ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner firstEdge first) (outer.cellVertex inner lastEdge last) := by
  obtain ⟨firstSide, firstReachable, firstBound⟩ := weighted_cell_available_anchor_near outer inner configuration cost
    nonnegative firstEdge first firstAvailable
  obtain ⟨lastSide, lastReachable, lastBound⟩ := weighted_cell_available_anchor_near outer inner configuration cost
    nonnegative lastEdge last lastAvailable
  exact ⟨firstSide, lastSide, firstReachable, lastReachable,
    (add_le_add firstBound lastBound).trans (weighted_distinct_cells_boundary_separation outer inner configuration
      cost nonnegative firstEdge lastEdge distinct first last reachable)⟩

end
end IGSIII34.ResistanceLimit
