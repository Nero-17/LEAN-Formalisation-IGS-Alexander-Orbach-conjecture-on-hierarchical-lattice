import IGSIII.Geometry.CellLocalisationBlockSeparation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

def signedComponentBoundaryDistance (graph : SimpleGraph Vertex) (source target point : Vertex) : ℝ := by
  classical
  exact if graph.Reachable source point then componentBoundaryDistance graph source target point
  else -componentBoundaryDistance graph source target point

@[simp] theorem signedComponentBoundaryDistance_source (graph : SimpleGraph Vertex) (source target : Vertex) :
    signedComponentBoundaryDistance graph source target source = 0 := by
  simp only [signedComponentBoundaryDistance, componentBoundaryDistance_source, ite_self, neg_zero]

@[simp] theorem signedComponentBoundaryDistance_target (graph : SimpleGraph Vertex) (source target : Vertex) :
    signedComponentBoundaryDistance graph source target target = 0 := by
  simp only [signedComponentBoundaryDistance, componentBoundaryDistance_target, neg_zero, ite_self]

theorem signedComponentBoundaryDistance_adj (graph : SimpleGraph Vertex) (source target : Vertex)
    {first last : Vertex} (adjacent : graph.Adj first last) :
    |signedComponentBoundaryDistance graph source target first - signedComponentBoundaryDistance graph source target last| ≤ 1 := by
  have same_component := reachable_adj_iff graph adjacent source
  by_cases reached : graph.Reachable source first
  · simp only [signedComponentBoundaryDistance, if_pos reached, if_pos (same_component.mp reached)]
    exact componentBoundaryDistance_adj graph source target adjacent
  · have last_unreached : ¬ graph.Reachable source last := fun reached_last => reached (same_component.mpr reached_last)
    simp only [signedComponentBoundaryDistance, if_neg reached, if_neg last_unreached]
    have identity : -componentBoundaryDistance graph source target first - -componentBoundaryDistance graph source target last =
      -(componentBoundaryDistance graph source target first - componentBoundaryDistance graph source target last) := by ring
    rw [identity, abs_neg]
    exact componentBoundaryDistance_adj graph source target adjacent

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

def signedCellBoundaryPotential (configuration : Fin outerEdges → Configuration innerEdges) :
    outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun edge point =>
    signedComponentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target point)

@[simp] theorem signedCellBoundaryPotential_cell (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (point : Fin innerVertices) :
    signedCellBoundaryPotential outer inner configuration (outer.cellVertex inner edge point) =
      signedComponentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target point := by
  exact outer.substitutionPotential_cell inner (fun _ => 0) _
    (fun _ => signedComponentBoundaryDistance_source _ _ _) (fun _ => signedComponentBoundaryDistance_target _ _ _) edge point

theorem signedCellBoundaryPotential_adj (configuration : Fin outerEdges → Configuration innerEdges)
    {first last : outer.SubstitutionVertex inner} (adjacent : (outer.substitutedGraph inner configuration).Adj first last) :
    |signedCellBoundaryPotential outer inner configuration first - signedCellBoundaryPotential outer inner configuration last| ≤ 1 := by
  obtain ⟨_, edge, left, right, localAdjacent, rfl, rfl⟩ := adjacent
  rw [signedCellBoundaryPotential_cell, signedCellBoundaryPotential_cell]
  exact signedComponentBoundaryDistance_adj _ _ _ localAdjacent

/-- The two sides of the same actual noncrossing cell pay both boundary
radii, even when their endpoints are joined through the exterior network. -/
theorem open_noncrossing_sides_boundary_separation (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (left right : Fin innerVertices)
    (noncrossing : ¬ (inner.openGraph (configuration edge)).Reachable inner.source inner.target)
    (left_reached : (inner.openGraph (configuration edge)).Reachable inner.source left)
    (right_reached : (inner.openGraph (configuration edge)).Reachable inner.target right)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner edge left) (outer.cellVertex inner edge right)) :
    componentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target left +
      componentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target right ≤
      ((outer.substitutedGraph inner configuration).dist
        (outer.cellVertex inner edge left) (outer.cellVertex inner edge right) : ℝ) := by
  have right_not_source : ¬ (inner.openGraph (configuration edge)).Reachable inner.source right :=
    fun source_reached => noncrossing (source_reached.trans right_reached.symm)
  have bound := graph_height_distance_bound (outer.substitutedGraph inner configuration)
    (signedCellBoundaryPotential outer inner configuration)
    (signedCellBoundaryPotential_adj outer inner configuration) reachable
  rw [signedCellBoundaryPotential_cell, signedCellBoundaryPotential_cell] at bound
  simpa only [signedComponentBoundaryDistance, if_pos left_reached, if_neg right_not_source, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg (componentBoundaryDistance_nonneg _ _ _ _) (componentBoundaryDistance_nonneg _ _ _ _))] using bound

end
end IGSIII.Geometry

