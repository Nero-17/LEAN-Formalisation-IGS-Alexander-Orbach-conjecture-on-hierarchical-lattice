import IGSIII.Geometry.CellLocalisationWeighted
import Mathlib.Algebra.Order.Group.MinMax

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem weightedComponentBoundaryDistance_le_source (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target point : Vertex) (reachable : graph.Reachable point source) :
    weightedComponentBoundaryDistance graph cost source target point ≤ weightedDistance graph cost point source := by
  classical
  rw [weightedDistance_comm graph cost nonnegative point source]
  simp only [weightedComponentBoundaryDistance, if_pos reachable.symm]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem weightedComponentBoundaryDistance_le_target (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target point : Vertex) (reachable : graph.Reachable point target) :
    weightedComponentBoundaryDistance graph cost source target point ≤ weightedDistance graph cost point target := by
  classical
  rw [weightedDistance_comm graph cost nonnegative point target]
  simp only [weightedComponentBoundaryDistance, if_pos reachable.symm]
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

/-- The actual distance cone rooted at an interior point and cut off before
the planted boundary. It is zero on components disjoint from the root. -/
def weightedBoundaryCone (graph : SimpleGraph Vertex) (cost : Sym2 Vertex → ℝ)
    (source target root point : Vertex) : ℝ := by
  classical
  exact if graph.Reachable root point then
    max (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root point) 0
  else 0

@[simp] theorem weightedBoundaryCone_source (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target root : Vertex) : weightedBoundaryCone graph cost source target root source = 0 := by
  classical
  by_cases reachable : graph.Reachable root source
  · simp only [weightedBoundaryCone, if_pos reachable]
    exact max_eq_right (sub_nonpos.mpr (weightedComponentBoundaryDistance_le_source graph cost nonnegative source target root reachable))
  · simp only [weightedBoundaryCone, if_neg reachable]

@[simp] theorem weightedBoundaryCone_target (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target root : Vertex) : weightedBoundaryCone graph cost source target root target = 0 := by
  classical
  by_cases reachable : graph.Reachable root target
  · simp only [weightedBoundaryCone, if_pos reachable]
    exact max_eq_right (sub_nonpos.mpr (weightedComponentBoundaryDistance_le_target graph cost nonnegative source target root reachable))
  · simp only [weightedBoundaryCone, if_neg reachable]

theorem weightedBoundaryCone_adj (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target root : Vertex) {first second : Vertex} (adjacent : graph.Adj first second) :
    |weightedBoundaryCone graph cost source target root first - weightedBoundaryCone graph cost source target root second| ≤
      cost s(first, second) := by
  classical
  have reachability := reachable_adj_iff graph adjacent root
  by_cases first_reached : graph.Reachable root first
  · have second_reached := reachability.mp first_reached
    simp only [weightedBoundaryCone, if_pos first_reached, if_pos second_reached]
    have cone_bound := abs_max_sub_max_le_abs
      (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root first)
      (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root second) 0
    have identity :
        (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root first) -
          (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root second) =
        -(weightedDistance graph cost root first - weightedDistance graph cost root second) := by ring
    rw [identity, abs_neg] at cone_bound
    exact cone_bound.trans (weightedDistance_adj_bound graph cost nonnegative root adjacent)
  · have second_unreached : ¬ graph.Reachable root second := fun reached => first_reached (reachability.mpr reached)
    simpa only [weightedBoundaryCone, if_neg first_reached, if_neg second_unreached, sub_self, abs_zero] using
      nonnegative s(first, second)

theorem weightedBoundaryCone_root_difference (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (source target root point : Vertex) (reachable : graph.Reachable root point) :
    |weightedBoundaryCone graph cost source target root root - weightedBoundaryCone graph cost source target root point| =
      min (weightedComponentBoundaryDistance graph cost source target root) (weightedDistance graph cost root point) := by
  classical
  simp only [weightedBoundaryCone, if_pos (SimpleGraph.Reachable.refl root), if_pos reachable,
    weightedDistance_self _ _ nonnegative, sub_zero,
    max_eq_left (weightedComponentBoundaryDistance_nonneg graph cost nonnegative source target root)]
  have radius_nonnegative := weightedComponentBoundaryDistance_nonneg graph cost nonnegative source target root
  have distance_nonnegative := weightedDistance_nonneg graph cost nonnegative root point
  by_cases radius_small : weightedComponentBoundaryDistance graph cost source target root ≤ weightedDistance graph cost root point
  · rw [max_eq_right (sub_nonpos.mpr radius_small), sub_zero, abs_of_nonneg radius_nonnegative, min_eq_left radius_small]
  · have distance_small := (le_of_not_ge radius_small)
    rw [max_eq_left (sub_nonneg.mpr distance_small), min_eq_right distance_small]
    have identity : weightedComponentBoundaryDistance graph cost source target root -
        (weightedComponentBoundaryDistance graph cost source target root - weightedDistance graph cost root point) =
          weightedDistance graph cost root point := by ring
    rw [identity, abs_of_nonneg distance_nonnegative]

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

def cellSupportedPotential (edge : Fin outerEdges) (height : Fin innerVertices → ℝ) :
    outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun other point => if other = edge then height point else 0)

theorem cellSupportedPotential_cell (edge : Fin outerEdges) (height : Fin innerVertices → ℝ)
    (source_zero : height inner.source = 0) (target_zero : height inner.target = 0)
    (other : Fin outerEdges) (point : Fin innerVertices) :
    cellSupportedPotential outer inner edge height (outer.cellVertex inner other point) =
      if other = edge then height point else 0 := by
  apply outer.substitutionPotential_cell inner (fun _ => 0)
  · intro other
    split_ifs <;> simp only [source_zero]
  · intro other
    split_ifs <;> simp only [target_zero]

theorem weighted_cell_supported_potential_bound
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) (height : Fin innerVertices → ℝ)
    (source_zero : height inner.source = 0) (target_zero : height inner.target = 0)
    (local_bound : ∀ {first second}, (inner.openGraph (configuration edge)).Adj first second →
      |height first - height second| ≤ cellBondCost outer inner cost edge s(first, second))
    {first last : Fin innerVertices} (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    |height first - height last| ≤ weightedDistance (outer.substitutedGraph inner configuration) cost
      (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) := by
  have bound := weighted_potential_distance_bound (outer.substitutedGraph inner configuration) cost
    (cellSupportedPotential outer inner edge height) (by
      intro first second adjacent
      obtain ⟨_, other, left, right, local_adjacent, rfl, rfl⟩ := adjacent
      rw [cellSupportedPotential_cell outer inner edge height source_zero target_zero,
        cellSupportedPotential_cell outer inner edge height source_zero target_zero]
      by_cases selected : other = edge
      · subst other
        simp only [if_true]
        exact local_bound local_adjacent
      · simp only [if_neg selected, sub_self, abs_zero]
        exact nonnegative _) (reachable.map (outer.cellHom inner configuration edge))
  change |cellSupportedPotential outer inner edge height (outer.cellVertex inner edge first) -
    cellSupportedPotential outer inner edge height (outer.cellVertex inner edge last)| ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) at bound
  simpa only [cellSupportedPotential_cell outer inner edge height source_zero target_zero, if_true] using bound

/-- Quantitative localisation inside a genuine weighted cell. In particular,
an interior point cannot be identified with a different intrinsic point by an
ambient shortcut. -/
theorem weighted_intrinsic_cell_localisation
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (outer.SubstitutionVertex inner) → ℝ) (nonnegative : ∀ bond, 0 ≤ cost bond)
    (edge : Fin outerEdges) {first last : Fin innerVertices}
    (reachable : (inner.openGraph (configuration edge)).Reachable first last) :
    min (weightedComponentBoundaryDistance (inner.openGraph (configuration edge))
        (cellBondCost outer inner cost edge) inner.source inner.target first)
      (weightedDistance (inner.openGraph (configuration edge)) (cellBondCost outer inner cost edge) first last) ≤
      weightedDistance (outer.substitutedGraph inner configuration) cost
        (outer.cellVertex inner edge first) (outer.cellVertex inner edge last) := by
  have local_nonnegative : ∀ bond, 0 ≤ cellBondCost outer inner cost edge bond := fun bond =>
    nonnegative (bond.map (outer.cellVertex inner edge))
  have bound := weighted_cell_supported_potential_bound outer inner configuration cost nonnegative edge
    (weightedBoundaryCone (inner.openGraph (configuration edge)) (cellBondCost outer inner cost edge)
      inner.source inner.target first)
    (weightedBoundaryCone_source _ _ local_nonnegative _ _ _)
    (weightedBoundaryCone_target _ _ local_nonnegative _ _ _)
    (fun adjacent => weightedBoundaryCone_adj _ _ local_nonnegative _ _ _ adjacent) reachable
  rwa [weightedBoundaryCone_root_difference _ _ local_nonnegative _ _ _ _ reachable] at bound

end
end IGSIII.Geometry


