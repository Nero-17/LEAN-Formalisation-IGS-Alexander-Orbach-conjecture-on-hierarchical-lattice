import Universality.Graph.Substitution
import Universality.Percolation.Bernoulli

/-!
# Bernoulli law under edge substitution

The connectedness indicators of independent cells are independent Bernoulli
variables with parameter equal to the cell reliability.  Combined with the
graph gluing theorem, this gives the reliability-composition identity for
the actual substituted graph.
-/

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

theorem local_coarse_weight (p : ℝ) (opened : Bool) :
    (∑ ω : Configuration innerEdges,
      if S.crosses ω = opened then bernoulliWeight p ω else 0) =
      if opened then S.reliability p else 1 - S.reliability p := by
  cases opened
  · rw [← sum_bernoulliWeight (edges := innerEdges) p]
    unfold reliability
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    cases h : S.crosses ω <;> simp
  · rfl

theorem coarse_configuration_weight (p : ℝ) (coarse : Configuration outerEdges) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) =
      bernoulliWeight (S.reliability p) coarse := by
  classical
  have fiber : (∑ ω : Fin outerEdges → Configuration innerEdges,
      if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) =
      ∏ e : Fin outerEdges, ∑ cell : Configuration innerEdges,
        if S.crosses cell = coarse e then bernoulliWeight p cell else 0 := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro ω _
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
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [he]
  rw [fiber]
  simp_rw [S.local_coarse_weight]
  rfl

theorem coarse_expectation (p : ℝ) (response : Configuration outerEdges → ℝ) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      (∏ e, bernoulliWeight p (ω e)) * response (S.coarseConfiguration ω)) =
      ∑ coarse : Configuration outerEdges,
        bernoulliWeight (S.reliability p) coarse * response coarse := by
  classical
  have expand (ω : Fin outerEdges → Configuration innerEdges) :
      (∏ e, bernoulliWeight p (ω e)) * response (S.coarseConfiguration ω) =
        ∑ coarse : Configuration outerEdges,
          (if S.coarseConfiguration ω = coarse then ∏ e, bernoulliWeight p (ω e) else 0) *
            response coarse := by
    simp [ite_mul]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [← Finset.sum_mul, coarse_configuration_weight]

def substitutedReliability (p : ℝ) : ℝ := by
  classical
  exact ∑ ω : Fin outerEdges → Configuration innerEdges,
    if (R.substitutedGraph S ω).Reachable (Sum.inl R.source) (Sum.inl R.target)
    then ∏ e, bernoulliWeight p (ω e) else 0

theorem substitutedReliability_eq (p : ℝ) :
    R.substitutedReliability S p = R.reliability (S.reliability p) := by
  classical
  unfold substitutedReliability
  simp_rw [substitutedReachable_iff, ← crosses_eq_true]
  have h := S.coarse_expectation p
    (fun coarse : Configuration outerEdges => if R.crosses coarse then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, reliability] using h

end
end Universality.FiniteNetwork
