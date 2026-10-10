import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
open Finset
noncomputable section

theorem uniform_positive_products_of_summable_loss
    (factor : ℕ → ℝ) (hpositive : ∀ n, 0 < factor n)
    (hsummable : Summable (fun n => 1 - factor n)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ n, lower ≤ ∏ i ∈ range n, factor i := by
  have hlog : Summable (fun n => Real.log (factor n)) := by
    have h := Real.summable_log_one_add_of_summable hsummable.neg
    convert h using 1
    ext n
    congr 1
    ring
  refine ⟨Real.exp (-∑' n, |Real.log (factor n)|), Real.exp_pos _, ?_⟩
  intro n
  have hsum : -(∑' i, |Real.log (factor i)|) ≤ ∑ i ∈ range n, Real.log (factor i) := by
    have hfirst := Finset.sum_le_sum (s := range n)
      (fun i _ => neg_abs_le (Real.log (factor i)))
    have hsecond := hlog.abs.sum_le_tsum (range n) (fun i _ => abs_nonneg (Real.log (factor i)))
    rw [Finset.sum_neg_distrib] at hfirst
    linarith
  have hexp := Real.exp_le_exp.mpr hsum
  simpa only [Real.exp_sum, Real.exp_log (hpositive _)] using hexp

theorem positive_lower_of_multiplicative_recursion
    (factor values : ℕ → ℝ) (order : ℕ)
    (hpositive : ∀ n, 0 < factor n) (hsummable : Summable (fun n => 1 - factor n))
    (hstart : 0 < values 0)
    (hstep : ∀ n, factor n ^ order * values n ≤ values (n + 1)) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ n, lower ≤ values n := by
  obtain ⟨lower, hlower, hbound⟩ := uniform_positive_products_of_summable_loss factor hpositive hsummable
  have hproduct (n : ℕ) : (∏ i ∈ range n, factor i) ^ order * values 0 ≤ values n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ = factor n ^ order * ((∏ i ∈ range n, factor i) ^ order * values 0) := by
          rw [Finset.prod_range_succ, mul_pow]
          ring
        _ ≤ factor n ^ order * values n := mul_le_mul_of_nonneg_left ih (pow_nonneg (hpositive n).le _)
        _ ≤ _ := hstep n
  refine ⟨lower ^ order * values 0, mul_pos (pow_pos hlower _) hstart, ?_⟩
  intro n
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlower.le (hbound n) order) hstart.le).trans (hproduct n)

end
end Universality

