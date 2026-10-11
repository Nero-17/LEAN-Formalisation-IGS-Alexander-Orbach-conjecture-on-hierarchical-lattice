import IGSIII34.ResistanceLimit.PairTriangle
import IGSIII34.Resistance.CurrentBound
import IGSIII34.Resistance.PathTrial
import IGSIII34.Percolation.Network
import IGSIII.Geometry.ActualSkeletonMetric

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem pairResistance_le_sum (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (first last : Vertex) (reachable : network.graph.Reachable first last) :
    pairResistance network resistance first last ≤ ∑ edge, resistance edge := by
  by_cases distinct : first ≠ last
  · rw [pairResistance, dif_pos distinct]
    obtain ⟨current, unitFlow, minimal⟩ :=
      (retarget network first last distinct).exists_minimizing_unitFlow_of_connected reachable positive
    rw [← minimal]
    apply Finset.sum_le_sum
    intro edge _
    have currentBound := (retarget network first last distinct).minimizing_current_abs_le_one positive unitFlow minimal edge
    have squareBound : current edge ^ 2 ≤ 1 := by
      simpa only [one_pow] using sq_le_sq.mpr (show |current edge| ≤ |(1 : ℝ)| by simpa using currentBound)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left squareBound (positive edge).le
  · simp only [pairResistance, dif_neg distinct]
    exact Finset.sum_nonneg (fun edge _ => (positive edge).le)

theorem pairResistance_unit_le_distance (network : Resistance.FiniteNetwork Vertex Edge)
    (first last : Vertex) (reachable : network.graph.Reachable first last) :
    pairResistance network (fun _ => 1) first last ≤ (network.graph.dist first last : ℝ) := by
  by_cases distinct : first ≠ last
  · rw [pairResistance, dif_pos distinct]
    exact (retarget network first last distinct).unitResistance_le_distance reachable
  · have equal := not_ne_iff.mp distinct
    subst last
    simp [pairResistance_self]

/-- The actual full source component with its electrical metric, on exactly
the same vertex type used by the chemical skeleton construction. -/
@[reducible] def actualComponentResistanceMetric {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    MetricSpace (IGSIII.Geometry.RetainedSkeletonVertex network configuration) where
  dist first last := pairResistance (IGSIII34.Percolation.network network configuration) resistance first.val last.val
  dist_self first := pairResistance_self _ _ _
  dist_comm first last := pairResistance_comm _ _ positive (by
    rw [IGSIII34.Percolation.graph_eq_openGraph]
    exact first.property.symm.trans last.property)
  dist_triangle first middle last := pairResistance_triangle _ _ positive _ _ _ (by
    rw [IGSIII34.Percolation.graph_eq_openGraph]
    exact first.property.symm.trans middle.property) (by
    rw [IGSIII34.Percolation.graph_eq_openGraph]
    exact middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := by
    intro first last zero
    apply Subtype.ext
    by_contra distinct
    have strict := pairResistance_pos (IGSIII34.Percolation.network network configuration) resistance positive distinct (by
      rw [IGSIII34.Percolation.graph_eq_openGraph]
      exact first.property.symm.trans last.property)
    exact (ne_of_gt strict) zero

end
end IGSIII34.ResistanceLimit
