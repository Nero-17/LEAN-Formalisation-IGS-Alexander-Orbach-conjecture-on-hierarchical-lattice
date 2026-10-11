import Universality.Section5.HeterogeneousReliability
import Universality.Percolation.ProductDisintegration

/-! Product disintegration for genuinely edge-dependent child networks.
The response is indexed by the child as well, avoiding artificial padding or
identification of differently sized configuration spaces. -/

namespace Universality
open scoped BigOperators

theorem finite_dependent_product_local_moment {ι : Type*} {α : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (α i)]
    (weight response : (i : ι) → α i → ℝ) (edge : ι) :
    (∑ configuration : (i : ι) → α i,
      (∏ i, weight i (configuration i)) * response edge (configuration edge)) =
      (∏ i ∈ Finset.univ.erase edge, ∑ value, weight i value) *
        (∑ value, weight edge value * response edge value) := by
  classical
  have factor (configuration : (i : ι) → α i) :
      (∏ i, weight i (configuration i)) * response edge (configuration edge) =
      ∏ i, weight i (configuration i) *
        (if i = edge then response i (configuration i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [factor]
  rw [← Fintype.prod_sum
    (fun i value => weight i value * (if i = edge then response i value else 1))]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ edge)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i member
    simp [Finset.ne_of_mem_erase member]
  · simp

namespace FiniteNetwork
noncomputable section

variable {outerEdges : ℕ} {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

theorem heterogeneous_coarse_fiber_cell_moment (p : ℝ) (coarse : Configuration outerEdges)
    (edge : Fin outerEdges)
    (response : (edge : Fin outerEdges) → Configuration (innerEdges edge) → ℝ) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      if heterogeneousCoarseConfiguration S configuration = coarse then
        (∏ edge, bernoulliWeight p (configuration edge)) * response edge (configuration edge)
      else 0) =
      (∏ other ∈ Finset.univ.erase edge,
        if coarse other then (S other).reliability p else 1 - (S other).reliability p) *
      (∑ cell : Configuration (innerEdges edge),
        if (S edge).crosses cell = coarse edge then bernoulliWeight p cell * response edge cell
        else 0) := by
  classical
  have factor (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
      (if heterogeneousCoarseConfiguration S configuration = coarse then
        (∏ edge, bernoulliWeight p (configuration edge)) * response edge (configuration edge)
       else 0) =
      (∏ edge, if (S edge).crosses (configuration edge) = coarse edge
        then bernoulliWeight p (configuration edge) else 0) * response edge (configuration edge) := by
    by_cases equality : heterogeneousCoarseConfiguration S configuration = coarse
    · subst coarse
      simp [heterogeneousCoarseConfiguration]
    · rw [if_neg equality]
      have different : ∃ edge, (S edge).crosses (configuration edge) ≠ coarse edge := by
        by_contra none
        apply equality
        funext edge
        exact not_not.mp (fun mismatch => none ⟨edge, mismatch⟩)
      obtain ⟨other, mismatch⟩ := different
      have zero : (∏ edge, if (S edge).crosses (configuration edge) = coarse edge
          then bernoulliWeight p (configuration edge) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ other)
        simp [mismatch]
      rw [zero, zero_mul]
  simp_rw [factor]
  rw [finite_dependent_product_local_moment
    (fun edge cell => if (S edge).crosses cell = coarse edge then bernoulliWeight p cell else 0)
    response edge]
  simp_rw [local_coarse_weight, ite_mul, zero_mul]

theorem heterogeneous_coarse_fiber_conditional_response (p : ℝ)
    (positive : ∀ edge, 0 < (S edge).reliability p)
    (less : ∀ edge, (S edge).reliability p < 1)
    (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (response : (edge : Fin outerEdges) → Configuration (innerEdges edge) → ℝ) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      if heterogeneousCoarseConfiguration S configuration = coarse then
        (∏ edge, bernoulliWeight p (configuration edge)) * response edge (configuration edge)
      else 0) =
      (∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p) *
        (S edge).conditionalCellResponse p (coarse edge) (response edge) := by
  rw [heterogeneous_coarse_fiber_cell_moment]
  unfold conditionalCellResponse
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ edge)]
  have nonzero : (if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p) ≠ 0 := by
    cases coarse edge <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ne_of_gt (sub_pos.mpr (less edge))
    · exact ne_of_gt (positive edge)
  rw [mul_assoc, mul_div_cancel₀ _ nonzero]

theorem heterogeneous_coarse_cell_expectation (p : ℝ)
    (positive : ∀ edge, 0 < (S edge).reliability p)
    (less : ∀ edge, (S edge).reliability p < 1)
    (edge : Fin outerEdges)
    (response : Configuration outerEdges →
      (edge : Fin outerEdges) → Configuration (innerEdges edge) → ℝ) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      (∏ edge, bernoulliWeight p (configuration edge)) *
        response (heterogeneousCoarseConfiguration S configuration) edge (configuration edge)) =
    ∑ coarse : Configuration outerEdges,
      (∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p) *
        (S edge).conditionalCellResponse p (coarse edge) (response coarse edge) := by
  classical
  have expansion (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
      (∏ edge, bernoulliWeight p (configuration edge)) *
        response (heterogeneousCoarseConfiguration S configuration) edge (configuration edge) =
      ∑ coarse : Configuration outerEdges,
        if heterogeneousCoarseConfiguration S configuration = coarse then
          (∏ edge, bernoulliWeight p (configuration edge)) * response coarse edge (configuration edge)
        else 0 := by simp
  simp_rw [expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  exact heterogeneous_coarse_fiber_conditional_response S p positive less coarse edge (response coarse)

end
end FiniteNetwork
end Universality
