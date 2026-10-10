import Universality.Percolation.MultilevelLaw

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Off-critical disintegration uses the effective parameter in the coarse
network. No stationarity or fixed-point assumption is imposed. -/
theorem conditional_substitution_joint_weight_effective
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened : Bool) (coarse : Configuration outerEdges)
    (cells : Fin outerEdges → Configuration innerEdges) :
    R.conditionalCellWeight (S.reliability p) opened coarse *
        (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) =
      if S.coarseConfiguration cells = coarse then
        (R.substitute S).conditionalCellWeight p opened (substitutionConfigurationEquiv cells)
      else 0 := by
  classical
  rw [← S.coarse_fiber_conditional_joint_weight p coarse cells]
  by_cases hcoarse : S.coarseConfiguration cells = coarse
  · subst coarse
    rw [if_pos rfl, if_pos rfl]
    unfold conditionalCellWeight
    rw [R.substitute_reliability S, R.substitute_crosses S,
      bernoulliWeight_substitutionConfiguration]
    by_cases hroot : R.crosses (S.coarseConfiguration cells) = opened
    · simp only [if_pos hroot]
      rw [div_mul_div_comm]
      rw [mul_comm (if opened then R.reliability (S.reliability p) else
        1 - R.reliability (S.reliability p))]
      exact mul_div_mul_left _ _ (ne_of_gt (bernoulliWeight_pos hpositive hless _))
    · simp [hroot]
  · simp [hcoarse]

/-- Tower identity for an arbitrary observable retaining the whole coarse
configuration and every fine cell. -/
theorem conditional_substitution_observable
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened : Bool)
    (response : Configuration outerEdges → (Fin outerEdges → Configuration innerEdges) → ℝ) :
    (∑ cells, (R.substitute S).conditionalCellWeight p opened
        (substitutionConfigurationEquiv cells) * response (S.coarseConfiguration cells) cells) =
      ∑ coarse, R.conditionalCellWeight (S.reliability p) opened coarse *
        ∑ cells, (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) * response coarse cells := by
  classical
  symm
  simp only [Finset.mul_sum, ← mul_assoc]
  simp_rw [R.conditional_substitution_joint_weight_effective S p hpositive hless]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cells _
  simp only [ite_mul, zero_mul]
  simp

theorem conditional_product_mass (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) :
    ∑ cells : Fin outerEdges → Configuration innerEdges,
      ∏ e, S.conditionalCellWeight p (coarse e) (cells e) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [S.sum_conditionalCellWeight p hpositive hless, Finset.prod_const_one]

theorem conditional_product_cell_moment (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (response : Configuration innerEdges → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) * response (cells edge)) =
      ∑ cell, S.conditionalCellWeight p (coarse edge) cell * response cell := by
  rw [Universality.finite_product_local_moment]
  simp only [S.sum_conditionalCellWeight p hpositive hless, Finset.prod_const_one, one_mul]

theorem conditional_product_additive_response (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (reward : ℝ)
    (response : Fin outerEdges → Configuration innerEdges → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        (reward + ∑ e, response e (cells e))) =
      reward + ∑ e, ∑ cell, S.conditionalCellWeight p (coarse e) cell * response e cell := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, S.conditional_product_mass p hpositive hless, one_mul]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact S.conditional_product_cell_moment p hpositive hless coarse e (response e)

end
end Universality.FiniteNetwork
