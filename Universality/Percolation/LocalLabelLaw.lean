import Universality.Percolation.OrientedStates

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- The random EIGS replacement law of one oriented parent. It samples a
whole percolation configuration and then labels all offspring together. -/
def offspringLabelWeight (p : ℝ) (parent : OrientedState)
    (labels : Fin edges → OrientedState) : ℝ :=
  ∑ cell : Configuration edges,
    R.conditionalCellWeight p (decide (parent = .connected)) cell *
      (if R.orientedChildState parent.sourceSelected parent.targetSelected cell = labels then 1 else 0)

theorem offspringLabelWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (parent : OrientedState) (labels : Fin edges → OrientedState) :
    0 ≤ R.offspringLabelWeight p parent labels := by
  apply Finset.sum_nonneg
  intro cell _
  apply mul_nonneg (R.conditionalCellWeight_nonneg hp hp' _ cell)
  split <;> norm_num

theorem sum_offspringLabelWeight (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) (parent : OrientedState) :
    ∑ labels, R.offspringLabelWeight p parent labels = 1 := by
  classical
  unfold offspringLabelWeight
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero]
  simpa using R.sum_conditionalCellWeight p hpositive hless (decide (parent = .connected))

theorem inactive_offspringLabelWeight (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (labels : Fin edges → OrientedState) :
    R.offspringLabelWeight p .inactive labels =
      if labels = (fun _ => .inactive) then 1 else 0 := by
  classical
  have hlabels (cell : Configuration edges) :
      R.orientedChildState false false cell = fun _ => .inactive := by
    funext e
    exact R.inactive_has_no_live_children cell e
  simp only [offspringLabelWeight, OrientedState.sourceSelected, OrientedState.targetSelected,
    hlabels, ← Finset.sum_mul, R.sum_conditionalCellWeight p hpositive hless, one_mul]
  simp only [eq_comm]

/-- Once a live parent state is fixed, its crossing condition is fixed.
For an inactive parent both possible crossing conditions give the same
deterministic all-inactive offspring vector. -/
theorem conditioned_offspring_eq_parent_law (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened : Bool) (parent : OrientedState)
    (hstate : parent ≠ .inactive → (parent = .connected ↔ opened = true))
    (labels : Fin edges → OrientedState) :
    (∑ cell : Configuration edges, R.conditionalCellWeight p opened cell *
      (if R.orientedChildState parent.sourceSelected parent.targetSelected cell = labels then 1 else 0)) =
      R.offspringLabelWeight p parent labels := by
  classical
  by_cases hinactive : parent = .inactive
  · subst parent
    rw [R.inactive_offspringLabelWeight p hpositive hless]
    have hlabels (cell : Configuration edges) :
        R.orientedChildState false false cell = fun _ => .inactive := by
      funext e
      exact R.inactive_has_no_live_children cell e
    simp only [OrientedState.sourceSelected, OrientedState.targetSelected, hlabels,
      ← Finset.sum_mul, R.sum_conditionalCellWeight p hpositive hless, one_mul]
    simp only [eq_comm]
  · have hopen : decide (parent = .connected) = opened := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using hstate hinactive
    unfold offspringLabelWeight
    rw [hopen]

theorem conditionalCellResponse_eq_weighted_sum (p : ℝ) (opened : Bool)
    (response : Configuration edges → ℝ) :
    R.conditionalCellResponse p opened response =
      ∑ cell, R.conditionalCellWeight p opened cell * response cell := by
  unfold conditionalCellResponse conditionalCellWeight
  simp only [ite_mul, zero_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro cell _
  split <;> ring

theorem offspring_labels_conditionally_independent
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (hpositive : 0 < inner.reliability p) (hless : inner.reliability p < 1)
    (sourceSelected targetSelected : Bool) (coarse : Configuration outerEdges)
    (labels : Fin outerEdges → Fin innerEdges → OrientedState) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      ((if inner.coarseConfiguration cells = coarse then ∏ e, bernoulliWeight p (cells e) else 0) /
        bernoulliWeight (inner.reliability p) coarse) *
      ∏ e, if inner.orientedChildState
          (outer.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
          (outer.orientedChildState sourceSelected targetSelected coarse e).targetSelected (cells e) =
            labels e then 1 else 0) =
      ∏ e, inner.offspringLabelWeight p
        (outer.orientedChildState sourceSelected targetSelected coarse e) (labels e) := by
  classical
  rw [inner.coarse_fiber_joint_response p coarse
    (fun e cell => if inner.orientedChildState
      (outer.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
      (outer.orientedChildState sourceSelected targetSelected coarse e).targetSelected cell =
      labels e then 1 else 0)]
  apply Finset.prod_congr rfl
  intro e _
  rw [inner.conditionalCellResponse_eq_weighted_sum]
  exact inner.conditioned_offspring_eq_parent_law p hpositive hless (coarse e) _
    (fun hlive => outer.live_oriented_state_determines_crossing sourceSelected targetSelected coarse e hlive)
    (labels e)

end
end Universality.FiniteNetwork
