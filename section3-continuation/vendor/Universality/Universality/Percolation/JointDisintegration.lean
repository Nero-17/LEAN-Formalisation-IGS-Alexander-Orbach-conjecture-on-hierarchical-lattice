import Universality.Percolation.ProductDisintegration

/-!
# Joint conditional law of all cells

The full configuration weight on a coarse fibre factors into conditional cell
weights. This retains dependence inside each cell and proves independence
between cells, rather than only a first-moment identity.
-/

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

variable {outerEdges innerVertices innerEdges : ℕ}
variable (S : FiniteNetwork innerVertices innerEdges)

def conditionalCellWeight (p : ℝ) (opened : Bool)
    (cell : Configuration innerEdges) : ℝ :=
  (if S.crosses cell = opened then bernoulliWeight p cell else 0) /
    (if opened then S.reliability p else 1 - S.reliability p)

theorem sum_conditionalCellWeight (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened : Bool) :
    ∑ cell, S.conditionalCellWeight p opened cell = 1 := by
  unfold conditionalCellWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, S.local_coarse_weight]
  rw [← div_eq_mul_inv]
  apply div_self
  cases opened
  · exact ne_of_gt (sub_pos.mpr hless)
  · exact ne_of_gt hpositive

theorem conditionalCellWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (opened : Bool) (cell : Configuration innerEdges) :
    0 ≤ S.conditionalCellWeight p opened cell := by
  apply div_nonneg
  · split
    · exact bernoulliWeight_nonneg hp hp' cell
    · exact le_rfl
  · cases opened
    · exact sub_nonneg.mpr (S.reliability_le_one hp hp')
    · exact S.reliability_nonneg hp hp'

theorem coarse_fiber_weight_factor (p : ℝ) (coarse : Configuration outerEdges)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) =
      ∏ e, if S.crosses (ω e) = coarse e then bernoulliWeight p (ω e) else 0 := by
  classical
  by_cases h : S.coarseConfiguration ω = coarse
  · subst coarse
    simp [coarseConfiguration]
  · rw [if_neg h]
    symm
    have hex : ∃ e, S.crosses (ω e) ≠ coarse e := by
      by_contra hnone
      apply h
      funext e
      exact not_not.mp (fun he => hnone ⟨e, he⟩)
    obtain ⟨e, he⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- Equality of every atom of the conditional joint law. -/
theorem coarse_fiber_conditional_joint_weight (p : ℝ)
    (coarse : Configuration outerEdges)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) /
        bernoulliWeight (S.reliability p) coarse =
      ∏ e, S.conditionalCellWeight p (coarse e) (ω e) := by
  rw [S.coarse_fiber_weight_factor]
  simp only [conditionalCellWeight, Finset.prod_div_distrib, bernoulliWeight]

/-- Factorisation of arbitrary simultaneous cell observables, conditional on
the entire coarse configuration. In particular, indicators give every joint
event probability, not only individual marginal expectations. -/
theorem coarse_fiber_joint_response (p : ℝ)
    (coarse : Configuration outerEdges)
    (response : Fin outerEdges → Configuration innerEdges → ℝ) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      ((if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) /
        bernoulliWeight (S.reliability p) coarse) * ∏ e, response e (ω e)) =
      ∏ e, S.conditionalCellResponse p (coarse e) (response e) := by
  simp_rw [S.coarse_fiber_conditional_joint_weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e cell =>
    S.conditionalCellWeight p (coarse e) cell * response e cell)]
  apply Finset.prod_congr rfl
  intro e _
  unfold conditionalCellWeight conditionalCellResponse
  simp_rw [div_mul_eq_mul_div, ite_mul, zero_mul]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem critical_coarse_fiber_conditional_joint_weight (p : ℝ)
    (hfixed : S.reliability p = p) (coarse : Configuration outerEdges)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) /
        bernoulliWeight p coarse =
      ∏ e, S.conditionalCellWeight p (coarse e) (ω e) := by
  simpa only [hfixed] using S.coarse_fiber_conditional_joint_weight p coarse ω

end
end Universality.FiniteNetwork
