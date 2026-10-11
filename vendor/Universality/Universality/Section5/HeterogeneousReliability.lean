import Universality.Section5.HeterogeneousNetwork

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

theorem bernoulliWeight_heterogeneousConfiguration (p : ℝ)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    bernoulliWeight p (heterogeneousConfigurationEquiv configuration) =
      ∏ edge, bernoulliWeight p (configuration edge) := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sigma (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
    if configuration pair.1 pair.2 then p else 1 - p)]
  exact (Fintype.equivFin (Σ edge : Fin outerEdges, Fin (innerEdges edge))).symm.prod_comp
    (fun pair => if configuration pair.1 pair.2 then p else 1 - p)

theorem heterogeneous_coarse_weight (p : ℝ) (coarse : Configuration outerEdges) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      if heterogeneousCoarseConfiguration S configuration = coarse
      then ∏ edge, bernoulliWeight p (configuration edge) else 0) =
      ∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p := by
  classical
  have fiber :
      (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
        if heterogeneousCoarseConfiguration S configuration = coarse
        then ∏ edge, bernoulliWeight p (configuration edge) else 0) =
      ∏ edge : Fin outerEdges, ∑ cell : Configuration (innerEdges edge),
        if (S edge).crosses cell = coarse edge then bernoulliWeight p cell else 0 := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro configuration _
    by_cases equality : heterogeneousCoarseConfiguration S configuration = coarse
    · subst coarse
      simp [heterogeneousCoarseConfiguration]
    · rw [if_neg equality]
      symm
      have different : ∃ edge, (S edge).crosses (configuration edge) ≠ coarse edge := by
        by_contra none
        apply equality
        funext edge
        exact not_not.mp (fun mismatch => none ⟨edge, mismatch⟩)
      obtain ⟨edge, mismatch⟩ := different
      apply Finset.prod_eq_zero (Finset.mem_univ edge)
      simp [mismatch]
  rw [fiber]
  simp_rw [local_coarse_weight]

theorem heterogeneous_coarse_expectation (p : ℝ) (response : Configuration outerEdges → ℝ) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      (∏ edge, bernoulliWeight p (configuration edge)) *
        response (heterogeneousCoarseConfiguration S configuration)) =
      ∑ coarse : Configuration outerEdges,
        (∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p) *
          response coarse := by
  classical
  have expansion (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
      (∏ edge, bernoulliWeight p (configuration edge)) *
        response (heterogeneousCoarseConfiguration S configuration) =
      ∑ coarse : Configuration outerEdges,
        (if heterogeneousCoarseConfiguration S configuration = coarse
          then ∏ edge, bernoulliWeight p (configuration edge) else 0) * response coarse := by
    simp [ite_mul]
  simp_rw [expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [← Finset.sum_mul, heterogeneous_coarse_weight]

theorem heterogeneousSubstitute_reliability (p : ℝ) :
    (R.heterogeneousSubstitute S).reliability p =
      ∑ coarse : Configuration outerEdges,
        if R.crosses coarse then
          ∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p
        else 0 := by
  classical
  have transport : (R.heterogeneousSubstitute S).reliability p =
      ∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
        if R.crosses (heterogeneousCoarseConfiguration S configuration)
        then ∏ edge, bernoulliWeight p (configuration edge) else 0 := by
    unfold reliability
    symm
    apply Fintype.sum_equiv heterogeneousConfigurationEquiv
    intro configuration
    rw [heterogeneousSubstitute_crosses, bernoulliWeight_heterogeneousConfiguration]
  rw [transport]
  have expectation := heterogeneous_coarse_expectation S p
    (fun coarse => if R.crosses coarse then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero] using expectation

theorem heterogeneousSubstitute_reliability_common (p q : ℝ)
    (common : ∀ edge, (S edge).reliability p = q) :
    (R.heterogeneousSubstitute S).reliability p = R.reliability q := by
  rw [heterogeneousSubstitute_reliability]
  simp_rw [common]
  rfl

end
end Universality.FiniteNetwork
