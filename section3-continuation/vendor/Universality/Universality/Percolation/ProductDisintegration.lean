import Universality.Percolation.SubstitutionLaw

namespace Universality
open scoped BigOperators

theorem finite_product_local_moment {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (weight : ι → α → ℝ) (response : α → ℝ) (edge : ι) :
    (∑ ω : ι → α, (∏ i, weight i (ω i)) * response (ω edge)) =
      (∏ i ∈ Finset.univ.erase edge, ∑ a, weight i a) *
        (∑ a, weight edge a * response a) := by
  classical
  have factor (ω : ι → α) :
      (∏ i, weight i (ω i)) * response (ω edge) =
      ∏ i, weight i (ω i) * (if i = edge then response (ω i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [factor]
  rw [← Fintype.prod_sum (fun i a => weight i a * (if i = edge then response a else 1))]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ edge)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  · simp

namespace FiniteNetwork
noncomputable section

variable {outerEdges innerVertices innerEdges : ℕ}
variable (S : FiniteNetwork innerVertices innerEdges)

theorem coarse_fiber_cell_moment (p : ℝ) (coarse : Configuration outerEdges)
    (edge : Fin outerEdges) (response : Configuration innerEdges → ℝ) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      if S.coarseConfiguration ω = coarse then
        (∏ e, bernoulliWeight p (ω e)) * response (ω edge) else 0) =
      (∏ e ∈ Finset.univ.erase edge,
        if coarse e then S.reliability p else 1 - S.reliability p) *
      (∑ cell : Configuration innerEdges,
        if S.crosses cell = coarse edge then bernoulliWeight p cell * response cell else 0) := by
  classical
  have factor (ω : Fin outerEdges → Configuration innerEdges) :
      (if S.coarseConfiguration ω = coarse then
        (∏ e, bernoulliWeight p (ω e)) * response (ω edge) else 0) =
      (∏ e, if S.crosses (ω e) = coarse e then bernoulliWeight p (ω e) else 0) *
        response (ω edge) := by
    by_cases h : S.coarseConfiguration ω = coarse
    · subst coarse
      simp [coarseConfiguration]
    · rw [if_neg h]
      have hex : ∃ e, S.crosses (ω e) ≠ coarse e := by
        by_contra hnone
        apply h
        funext e
        exact not_not.mp (fun he => hnone ⟨e, he⟩)
      obtain ⟨e, he⟩ := hex
      have hz : (∏ e, if S.crosses (ω e) = coarse e then bernoulliWeight p (ω e) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp [he]
      rw [hz, zero_mul]
  simp_rw [factor]
  rw [finite_product_local_moment
    (fun e cell => if S.crosses cell = coarse e then bernoulliWeight p cell else 0)
    response edge]
  simp_rw [S.local_coarse_weight, ite_mul, zero_mul]

def conditionalCellResponse (p : ℝ) (opened : Bool)
    (response : Configuration innerEdges → ℝ) : ℝ :=
  (∑ cell : Configuration innerEdges,
    if S.crosses cell = opened then bernoulliWeight p cell * response cell else 0) /
    (if opened then S.reliability p else 1 - S.reliability p)

theorem coarse_fiber_conditional_response (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (response : Configuration innerEdges → ℝ) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      if S.coarseConfiguration ω = coarse then
        (∏ e, bernoulliWeight p (ω e)) * response (ω edge) else 0) =
      bernoulliWeight (S.reliability p) coarse *
        S.conditionalCellResponse p (coarse edge) response := by
  rw [S.coarse_fiber_cell_moment]
  unfold bernoulliWeight conditionalCellResponse
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ edge)]
  have hn : (if coarse edge then S.reliability p else 1 - S.reliability p) ≠ 0 := by
    cases coarse edge <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ne_of_gt (sub_pos.mpr hless)
    · exact ne_of_gt hpositive
  rw [mul_assoc, mul_div_cancel₀ _ hn]
  rfl

theorem coarse_cell_expectation (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (edge : Fin outerEdges)
    (response : Configuration outerEdges → Configuration innerEdges → ℝ) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      (∏ e, bernoulliWeight p (ω e)) * response (S.coarseConfiguration ω) (ω edge)) =
    ∑ coarse : Configuration outerEdges, bernoulliWeight (S.reliability p) coarse *
      S.conditionalCellResponse p (coarse edge) (response coarse) := by
  classical
  have expand (ω : Fin outerEdges → Configuration innerEdges) :
      (∏ e, bernoulliWeight p (ω e)) * response (S.coarseConfiguration ω) (ω edge) =
      ∑ coarse : Configuration outerEdges,
        if S.coarseConfiguration ω = coarse then
          (∏ e, bernoulliWeight p (ω e)) * response coarse (ω edge) else 0 := by
    simp
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  exact S.coarse_fiber_conditional_response p hpositive hless coarse edge (response coarse)

end
end FiniteNetwork
end Universality
