import Universality.Analysis.GeometricRecursionLimit

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem geometric_recursion_upper_bound (sequence error : ℕ → ℝ) (growth : ℝ)
    (hgrowth : 1 ≤ growth) (herror : ∀ n, 0 ≤ error n)
    (hrecursion : ∀ n, sequence (n + 1) ≤ growth * sequence n + error n)
    (hsummable : Summable error) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n, sequence n ≤ bound * growth ^ n := by
  have hgrowthPos : 0 < growth := lt_of_lt_of_le zero_lt_one hgrowth
  have hinduction (n : ℕ) : sequence n ≤
      (sequence 0 + ∑ i ∈ Finset.range n, error i) * growth ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ growth * sequence n + error n := hrecursion n
        _ ≤ growth * ((sequence 0 + ∑ i ∈ Finset.range n, error i) * growth ^ n) +
            error n * growth ^ (n + 1) := by
          exact add_le_add (mul_le_mul_of_nonneg_left ih hgrowthPos.le)
            (le_mul_of_one_le_right (herror n) (one_le_pow₀ hgrowth))
        _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring
  refine ⟨|sequence 0| + |∑' n, error n| + 1, by positivity, ?_⟩
  intro n
  apply (hinduction n).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hgrowthPos.le _)
  have hs := hsummable.sum_le_tsum (Finset.range n) (fun i _ => herror i)
  have hfirst := le_abs_self (sequence 0)
  have hsecond := le_abs_self (∑' n, error n)
  linarith

end
end Universality
