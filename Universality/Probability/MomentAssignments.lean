import Universality.Probability.MomentLinearPart

namespace Universality
noncomputable section
set_option maxHeartbeats 0

def assignmentMomentSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (moments : ι → ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ assignment : Fin r → ι, ∏ child,
    moments child (Fintype.card {a : Fin r // assignment a = child})

theorem assignmentMomentSum_linear_part {ι : Type*} [Fintype ι] [DecidableEq ι]
    (moments : ι → ℕ → ℝ) (hzero : ∀ child, moments child 0 = 1) (r : ℕ) (hr : 0 < r) :
    assignmentMomentSum moments r = (∑ child, moments child r) +
      ∑ assignment ∈ (Finset.univ.filter fun assignment : Fin r → ι =>
        ¬ ∃ child, assignment = fun _ => child),
        ∏ child, moments child (Fintype.card {a : Fin r // assignment a = child}) := by
  classical
  have hconstant : (Finset.univ.filter fun assignment : Fin r → ι => ∃ child, assignment = fun _ => child) =
      Finset.univ.image (fun child : ι => fun _ : Fin r => child) := by
    ext assignment
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simp only [eq_comm]
  unfold assignmentMomentSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun assignment : Fin r → ι => ∃ child, assignment = fun _ => child),
    hconstant]
  congr 1
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro child _
    rw [Finset.prod_eq_single child]
    · simp only [Fintype.card_subtype_true, Fintype.card_fin]
    · intro other _ hne
      simp [Ne.symm hne, hzero]
    · simp
  · intro first _ second _ heq
    exact congrFun heq ⟨0, hr⟩

theorem sum_assignment_fiber_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (assignment : Fin r → ι) :
    (∑ child, Fintype.card {a : Fin r // assignment a = child}) = r := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv assignment)).trans (Fintype.card_fin r)

theorem assignment_moment_product_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (moments : ι → ℕ → ℝ) (constant radius : ℝ) (hconstant : 0 ≤ constant) (hradius : 0 ≤ radius)
    (n k r : ℕ) (assignment : Fin k → ι)
    (hnonneg : ∀ child order, 0 ≤ moments child order)
    (hbound : ∀ child order, order < r → moments child order ≤ constant * radius ^ (order * n))
    (hlower : ∀ child, Fintype.card {a : Fin k // assignment a = child} < r) :
    (∏ child, moments child (Fintype.card {a : Fin k // assignment a = child})) ≤
      constant ^ Fintype.card ι * radius ^ (k * n) := by
  calc
    _ ≤ ∏ child, constant * radius ^ ((Fintype.card {a : Fin k // assignment a = child}) * n) := by
      apply Finset.prod_le_prod
      · intro child _
        exact hnonneg child _
      · intro child _
        exact hbound child _ (hlower child)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, sum_assignment_fiber_card]

end
end Universality
