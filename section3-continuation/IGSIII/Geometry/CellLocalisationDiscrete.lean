import IGSIII.Geometry.CellLocalisationCone
import IGSIII.Chemical.GraphPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

@[simp] theorem weightedDistance_unit_eq_dist (graph : SimpleGraph Vertex) (first last : Vertex) :
    weightedDistance graph (fun _ => 1) first last = (graph.dist first last : ℝ) := by
  classical
  by_cases reachable : graph.Reachable first last
  · rw [weightedDistance_of_reachable graph _ reachable, graphPathFamily_shortest_unit]
  · simp only [weightedDistance, dif_neg reachable, SimpleGraph.dist_eq_zero_of_not_reachable reachable, Nat.cast_zero]

@[simp] theorem weightedComponentBoundaryDistance_unit (graph : SimpleGraph Vertex) (source target point : Vertex) :
    weightedComponentBoundaryDistance graph (fun _ => 1) source target point =
      componentBoundaryDistance graph source target point := by
  unfold weightedComponentBoundaryDistance componentBoundaryDistance
  simp only [weightedDistance_unit_eq_dist]
  split_ifs <;> rfl

/-- The quantitative first-exit bound on actual unweighted microscopic cells.
It can therefore be passed to limits of their actual chemical metrics. -/
theorem intrinsic_cell_localisation {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges) (edge : Fin outerEdges)
    {first last : Fin innerVertices} (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    min (componentBoundaryDistance (inner.openGraph (configuration edge)) inner.source inner.target first)
      ((inner.openGraph (configuration edge)).dist first last : ℝ) ≤
        ((outer.substitutedGraph inner configuration).dist
          (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) : ℝ) := by
  have unit_cell_cost : cellBondCost outer inner (fun _ => (1 : ℝ)) edge = fun _ => 1 := rfl
  simpa only [unit_cell_cost, weightedComponentBoundaryDistance_unit, weightedDistance_unit_eq_dist] using
    weighted_intrinsic_cell_localisation outer inner configuration (fun _ => 1) (fun _ => zero_le_one) edge reachable

end
end IGSIII.Geometry


