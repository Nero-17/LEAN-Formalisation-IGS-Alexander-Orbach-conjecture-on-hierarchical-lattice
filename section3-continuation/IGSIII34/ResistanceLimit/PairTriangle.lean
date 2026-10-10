import IGSIII34.ResistanceLimit.PairResistance

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork

theorem reciprocal_sum_le_split (first second cut : ℝ) (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (first + second)⁻¹ ≤ cut ^ 2 / first + (1 - cut) ^ 2 / second := by
  have sumPositive : 0 < first + second := add_pos firstPositive secondPositive
  have remainder : 0 ≤ ((first + second) * cut - first) ^ 2 / (first * second * (first + second)) :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos firstPositive secondPositive) sumPositive).le
  have identity : cut ^ 2 / first + (1 - cut) ^ 2 / second - (first + second)⁻¹ =
      ((first + second) * cut - first) ^ 2 / (first * second * (first + second)) := by
    field_simp [firstPositive.ne', secondPositive.ne', sumPositive.ne']
    ring
  linarith

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem pairResistance_triangle (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (first middle last : Vertex)
    (firstReach : network.graph.Reachable first middle) (lastReach : network.graph.Reachable middle last) :
    pairResistance network resistance first last ≤
      pairResistance network resistance first middle + pairResistance network resistance middle last := by
  by_cases firstLast : first = last
  · subst last
    rw [pairResistance_self]
    exact add_nonneg (pairResistance_nonnegative network resistance positive firstReach)
      (pairResistance_nonnegative network resistance positive lastReach)
  by_cases firstMiddle : first = middle
  · subst middle
    simp [pairResistance_self]
  by_cases middleLast : middle = last
  · subst last
    simp [pairResistance_self]
  have firstPositive := pairResistance_pos network resistance positive firstMiddle firstReach
  have lastPositive := pairResistance_pos network resistance positive middleLast lastReach
  have totalPositive := pairResistance_pos network resistance positive firstLast (firstReach.trans lastReach)
  obtain ⟨potential, atFirst, atLast, range, minimal⟩ :=
    exists_pair_minimizer_in_unitInterval network resistance positive firstLast (firstReach.trans lastReach)
  have firstBound := pairResistance_energy_lower_bound network resistance positive firstMiddle firstReach
    (fun vertex => min (potential vertex) (potential middle))
  have lastBound := pairResistance_energy_lower_bound network resistance positive middleLast lastReach
    (fun vertex => max (potential vertex - potential middle) 0)
  rw [atFirst, min_eq_left (range middle).1, min_self, zero_sub, neg_sq] at firstBound
  rw [sub_self, max_self, atLast, max_eq_left (sub_nonneg.mpr (range middle).2), zero_sub, neg_sq] at lastBound
  have energySplit := split_potentialEnergy_le network resistance positive potential (potential middle)
  rw [minimal] at energySplit
  have reciprocalBound : (pairResistance network resistance first middle +
      pairResistance network resistance middle last)⁻¹ ≤ (pairResistance network resistance first last)⁻¹ :=
    (reciprocal_sum_le_split _ _ (potential middle) firstPositive lastPositive).trans
      ((add_le_add firstBound lastBound).trans energySplit)
  exact (inv_le_inv₀ (add_pos firstPositive lastPositive) totalPositive).mp reciprocalBound

/-- The effective-resistance metric on an actual connected component of the
same finite endpoint network. -/
@[reducible] def componentResistanceMetric (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (root : Vertex) :
    MetricSpace {vertex : Vertex // network.graph.Reachable root vertex} where
  dist first last := pairResistance network resistance first.val last.val
  dist_self first := pairResistance_self network resistance first.val
  dist_comm first last := pairResistance_comm network resistance positive (first.property.symm.trans last.property)
  dist_triangle first middle last := pairResistance_triangle network resistance positive _ _ _
    (first.property.symm.trans middle.property) (middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := by
    intro first last zero
    apply Subtype.ext
    by_contra different
    have strict := pairResistance_pos network resistance positive different (first.property.symm.trans last.property)
    exact (ne_of_gt strict) zero

end
end IGSIII34.ResistanceLimit
