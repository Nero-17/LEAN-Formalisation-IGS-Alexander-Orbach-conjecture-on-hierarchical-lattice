import IGSIII.Geometry.CellSeparation
import IGSIII.Chemical.WeightedGraphMetric

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- Weighted distance to the boundary of the actual retained component.
Unreachable terminals are excluded from the minimum. -/
def weightedComponentBoundaryDistance (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (source target point : Vertex) : ℝ := by
  classical
  exact if graph.Reachable source point then
    if graph.Reachable target point then
      min (weightedDistance graph cost source point) (weightedDistance graph cost target point)
    else weightedDistance graph cost source point
  else if graph.Reachable target point then weightedDistance graph cost target point else 0

theorem weightedComponentBoundaryDistance_nonneg (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target point : Vertex) :
    0 ≤ weightedComponentBoundaryDistance graph cost source target point := by
  unfold weightedComponentBoundaryDistance
  split_ifs
  · exact le_min (weightedDistance_nonneg _ _ nonnegative _ _) (weightedDistance_nonneg _ _ nonnegative _ _)
  · exact weightedDistance_nonneg _ _ nonnegative _ _
  · exact weightedDistance_nonneg _ _ nonnegative _ _
  · exact le_rfl

@[simp] theorem weightedComponentBoundaryDistance_source (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond) (source target : Vertex) :
    weightedComponentBoundaryDistance graph cost source target source = 0 := by
  simp [weightedComponentBoundaryDistance, weightedDistance_self _ _ nonnegative,
    weightedDistance_nonneg _ _ nonnegative]

@[simp] theorem weightedComponentBoundaryDistance_target (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond) (source target : Vertex) :
    weightedComponentBoundaryDistance graph cost source target target = 0 := by
  simp [weightedComponentBoundaryDistance, weightedDistance_self _ _ nonnegative,
    weightedDistance_nonneg _ _ nonnegative]

theorem weightedComponentBoundaryDistance_adj_le (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target : Vertex) {first second : Vertex} (adjacent : graph.Adj first second) :
    weightedComponentBoundaryDistance graph cost source target first ≤
      weightedComponentBoundaryDistance graph cost source target second + cost s(first, second) := by
  have sourceReach := reachable_adj_iff graph adjacent source
  have targetReach := reachable_adj_iff graph adjacent target
  have sourceBound := weightedDistance_adj_le graph cost nonnegative source adjacent
  have targetBound := weightedDistance_adj_le graph cost nonnegative target adjacent
  by_cases firstSource : graph.Reachable source first <;>
    by_cases firstTarget : graph.Reachable target first
  · have secondSource := sourceReach.mp firstSource
    have secondTarget := targetReach.mp firstTarget
    simp only [weightedComponentBoundaryDistance, if_pos firstSource, if_pos firstTarget,
      if_pos secondSource, if_pos secondTarget]
    exact (min_le_min sourceBound targetBound).trans_eq (min_add_add_right _ _ _)
  · have secondSource := sourceReach.mp firstSource
    have secondTarget : ¬ graph.Reachable target second := fun reached => firstTarget (targetReach.mpr reached)
    simpa only [weightedComponentBoundaryDistance, if_pos firstSource, if_neg firstTarget,
      if_pos secondSource, if_neg secondTarget] using sourceBound
  · have secondSource : ¬ graph.Reachable source second := fun reached => firstSource (sourceReach.mpr reached)
    have secondTarget := targetReach.mp firstTarget
    simpa only [weightedComponentBoundaryDistance, if_neg firstSource, if_pos firstTarget,
      if_neg secondSource, if_pos secondTarget] using targetBound
  · have secondSource : ¬ graph.Reachable source second := fun reached => firstSource (sourceReach.mpr reached)
    have secondTarget : ¬ graph.Reachable target second := fun reached => firstTarget (targetReach.mpr reached)
    simpa only [weightedComponentBoundaryDistance, if_neg firstSource, if_neg firstTarget,
      if_neg secondSource, if_neg secondTarget, zero_add] using nonnegative s(first, second)

theorem weightedComponentBoundaryDistance_adj (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target : Vertex) {first second : Vertex} (adjacent : graph.Adj first second) :
    |weightedComponentBoundaryDistance graph cost source target first -
      weightedComponentBoundaryDistance graph cost source target second| ≤ cost s(first, second) := by
  have forward := weightedComponentBoundaryDistance_adj_le graph cost nonnegative source target adjacent
  have backward := weightedComponentBoundaryDistance_adj_le graph cost nonnegative source target adjacent.symm
  rw [Sym2.eq_swap] at backward
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem weightedComponentBoundaryDistance_pos (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (positive : ∀ bond ∈ graph.edgeSet, 0 < cost bond) (source target point : Vertex)
    (notSource : point ≠ source) (notTarget : point ≠ target)
    (anchored : graph.Reachable source point ∨ graph.Reachable target point) :
    0 < weightedComponentBoundaryDistance graph cost source target point := by
  have sourcePositive (reachable : graph.Reachable source point) :
      0 < weightedDistance graph cost source point := by
    exact lt_of_le_of_ne (weightedDistance_nonneg _ _ nonnegative _ _) (fun zero =>
      notSource (eq_of_weightedDistance_eq_zero_of_edge_positive graph cost nonnegative positive reachable zero.symm).symm)
  have targetPositive (reachable : graph.Reachable target point) :
      0 < weightedDistance graph cost target point := by
    exact lt_of_le_of_ne (weightedDistance_nonneg _ _ nonnegative _ _) (fun zero =>
      notTarget (eq_of_weightedDistance_eq_zero_of_edge_positive graph cost nonnegative positive reachable zero.symm).symm)
  by_cases sourceReached : graph.Reachable source point <;>
    by_cases targetReached : graph.Reachable target point
  · simpa only [weightedComponentBoundaryDistance, if_pos sourceReached, if_pos targetReached] using
      lt_min (sourcePositive sourceReached) (targetPositive targetReached)
  · simpa only [weightedComponentBoundaryDistance, if_pos sourceReached, if_neg targetReached] using sourcePositive sourceReached
  · simpa only [weightedComponentBoundaryDistance, if_neg sourceReached, if_pos targetReached] using targetPositive targetReached
  · exact False.elim (anchored.elim sourceReached targetReached)

/-- An edgewise Lipschitz potential is bounded by the actual weighted
shortest path. This also applies to signed cell boundary heights. -/
theorem weighted_potential_distance_bound (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (height : Vertex → ℝ)
    (bounded : ∀ {first second}, graph.Adj first second →
      |height first - height second| ≤ cost s(first, second))
    {first last : Vertex} (reachable : graph.Reachable first last) :
    |height first - height last| ≤ weightedDistance graph cost first last := by
  have walk_bound : ∀ {first last : Vertex} (walk : graph.Walk first last),
      |height first - height last| ≤ (walk.edges.map cost).sum := by
    intro first last walk
    induction walk with
    | nil => simp
    | @cons first second last adjacent rest inductionHypothesis =>
      have triangle := abs_add_le (height first - height second) (height second - height last)
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
      have identity : height first - height second + (height second - height last) =
          height first - height last := by ring
      rw [identity] at triangle
      exact triangle.trans (add_le_add (bounded adjacent) inductionHypothesis)
  obtain ⟨walk, _, minimum⟩ := exists_weighted_geodesic graph cost reachable
  rw [← minimum]
  exact walk_bound walk

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

/-- Restrict the actual ambient bond cost to a particular child graph. -/
def cellBondCost (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ)
    (edge : Fin outerEdges) (bond : Sym2 (Fin innerVertices)) : ℝ :=
  cost (bond.map (outer.cellVertex inner edge))

/-- The inclusion of an actual cell decreases weighted distances, since every
intrinsic path is an ambient path with exactly the same edge costs. -/
theorem weighted_cell_distance_le (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) {first last : Fin innerVertices}
    (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    weightedDistance (outer.substitutedGraph inner configuration) cost
      (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) ≤
      weightedDistance (inner.openGraph (configuration edge)) (cellBondCost outer inner cost edge) first last := by
  obtain ⟨walk, _, minimum⟩ := exists_weighted_geodesic (inner.openGraph (configuration edge))
    (cellBondCost outer inner cost edge) reachable
  have bound := weightedDistance_le_walkCost (outer.substitutedGraph inner configuration) cost nonnegative
    (walk.map (outer.cellHom inner configuration edge))
  rw [SimpleGraph.Walk.edges_map, List.map_map] at bound
  change weightedDistance (outer.substitutedGraph inner configuration) cost
    (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) ≤
      (walk.edges.map (cellBondCost outer inner cost edge)).sum at bound
  rwa [minimum] at bound

def weightedCellBoundaryPotential (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (weight : Fin outerEdges → ℝ) :
    outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun edge point => weight edge *
    weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) inner.source inner.target point)

theorem weightedCellBoundaryPotential_cell (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (weight : Fin outerEdges → ℝ) (edge : Fin outerEdges) (point : Fin innerVertices) :
    weightedCellBoundaryPotential outer inner configuration cost weight (outer.cellVertex inner edge point) =
      weight edge * weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) inner.source inner.target point := by
  apply outer.substitutionPotential_cell inner (fun _ => 0)
  · intro edge
    rw [weightedComponentBoundaryDistance_source (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge)))]; simp
  · intro edge
    rw [weightedComponentBoundaryDistance_target (inner.openGraph (configuration edge))
      (cellBondCost outer inner cost edge) (fun bond => nonnegative (bond.map (outer.cellVertex inner edge)))]; simp

theorem weightedCellBoundaryPotential_adj (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (weight : Fin outerEdges → ℝ) (bounded : ∀ edge, |weight edge| ≤ 1)
    {first second : outer.SubstitutionVertex inner}
    (adjacent : (outer.substitutedGraph inner configuration).Adj first second) :
    |weightedCellBoundaryPotential outer inner configuration cost weight first -
      weightedCellBoundaryPotential outer inner configuration cost weight second| ≤ cost s(first, second) := by
  obtain ⟨_, edge, left, right, localAdjacent, rfl, rfl⟩ := adjacent
  rw [weightedCellBoundaryPotential_cell outer inner configuration cost nonnegative,
    weightedCellBoundaryPotential_cell outer inner configuration cost nonnegative, ← mul_sub, abs_mul]
  have localBound := weightedComponentBoundaryDistance_adj (inner.openGraph (configuration edge))
    (cellBondCost outer inner cost edge) (fun _ => nonnegative _) inner.source inner.target localAdjacent
  exact (mul_le_mul (bounded edge) localBound (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Distinct actual child components pay both intrinsic weighted distances to
their planted boundaries. Noncrossing and dangling components are retained. -/
theorem weighted_distinct_cells_boundary_separation
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (first second : Fin outerEdges) (distinct : first ≠ second) (left right : Fin innerVertices)
    (reachable : (outer.substitutedGraph inner configuration).Reachable
      (outer.cellVertex inner first left) (outer.cellVertex inner second right)) :
    weightedComponentBoundaryDistance (inner.openGraph (configuration first))
        (cellBondCost outer inner cost first) inner.source inner.target left +
      weightedComponentBoundaryDistance (inner.openGraph (configuration second))
        (cellBondCost outer inner cost second) inner.source inner.target right ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner first left) (outer.cellVertex inner second right) := by
  classical
  let weight (edge : Fin outerEdges) : ℝ := if edge = first then 1 else if edge = second then -1 else 0
  have bounded : ∀ edge, |weight edge| ≤ 1 := by
    intro edge
    dsimp only [weight]
    split_ifs <;> norm_num
  have bound := weighted_potential_distance_bound (outer.substitutedGraph inner configuration) cost
    (weightedCellBoundaryPotential outer inner configuration cost weight)
    (weightedCellBoundaryPotential_adj outer inner configuration cost nonnegative weight bounded) reachable
  rw [weightedCellBoundaryPotential_cell outer inner configuration cost nonnegative,
    weightedCellBoundaryPotential_cell outer inner configuration cost nonnegative] at bound
  have firstWeight : weight first = 1 := by simp [weight]
  have secondWeight : weight second = -1 := by simp [weight, distinct.symm]
  simpa only [firstWeight, secondWeight, one_mul, neg_one_mul, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg
      (weightedComponentBoundaryDistance_nonneg (inner.openGraph (configuration first))
        (cellBondCost outer inner cost first) (fun bond => nonnegative (bond.map (outer.cellVertex inner first))) _ _ _)
      (weightedComponentBoundaryDistance_nonneg (inner.openGraph (configuration second))
        (cellBondCost outer inner cost second) (fun bond => nonnegative (bond.map (outer.cellVertex inner second))) _ _ _))] using bound

end
end IGSIII.Geometry
