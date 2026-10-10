import Universality.Analysis.NormalizedLogIteration

namespace Universality
noncomputable section
set_option maxHeartbeats 0

theorem finite_growth_sum_bound (sequence : ℕ → ℝ) (lower : ℝ) (depth : ℕ)
    (hstep : ∀ n < depth, lower * sequence n ≤ sequence (n + 1)) :
    (lower - 1) * (∑ n ∈ Finset.range depth, sequence n) ≤ sequence depth - sequence 0 := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    have hprevious := ih (fun n hn => hstep n (by omega))
    have hlast := hstep depth (by omega)
    rw [Finset.sum_range_succ, mul_add]
    nlinarith

theorem finite_log_growth_sum (sequence : ℕ → ℝ) (multiplier : ℝ) (depth : ℕ) :
    (∑ n ∈ Finset.range depth,
      (Real.log (sequence (n + 1)) - Real.log (sequence n) - Real.log multiplier)) =
      Real.log (sequence depth) - Real.log (sequence 0) - (depth : ℝ) * Real.log multiplier := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The error remains uniformly bounded before escape because deviations
grow geometrically and their total is bounded by their final value. -/
theorem finite_log_growth_error_bound (sequence : ℕ → ℝ) (multiplier lower rate : ℝ) (depth : ℕ)
    (hlower : 1 < lower) (hrate : 0 ≤ rate) (hstart : 0 ≤ sequence 0)
    (hstep : ∀ n < depth, lower * sequence n ≤ sequence (n + 1))
    (herror : ∀ n < depth,
      |Real.log (sequence (n + 1)) - Real.log (sequence n) - Real.log multiplier| ≤ rate * sequence n) :
    |Real.log (sequence depth) - Real.log (sequence 0) - (depth : ℝ) * Real.log multiplier| ≤
      rate * sequence depth / (lower - 1) := by
  have hsum : (∑ n ∈ Finset.range depth, sequence n) ≤ sequence depth / (lower - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hlower)).mpr
    have h := finite_growth_sum_bound sequence lower depth hstep
    nlinarith
  rw [← finite_log_growth_sum sequence multiplier depth]
  calc
    _ ≤ ∑ n ∈ Finset.range depth,
        |Real.log (sequence (n + 1)) - Real.log (sequence n) - Real.log multiplier| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range depth, rate * sequence n :=
      Finset.sum_le_sum (fun n hn => herror n (Finset.mem_range.mp hn))
    _ = rate * ∑ n ∈ Finset.range depth, sequence n := (Finset.mul_sum ..).symm
    _ ≤ rate * (sequence depth / (lower - 1)) := mul_le_mul_of_nonneg_left hsum hrate
    _ = _ := by ring

theorem finite_escape_time_error_bound (sequence : ℕ → ℝ) (multiplier lower rate : ℝ) (depth : ℕ)
    (hlower : 1 < lower) (hrate : 0 ≤ rate) (hstart : 0 ≤ sequence 0)
    (hstep : ∀ n < depth, lower * sequence n ≤ sequence (n + 1))
    (herror : ∀ n < depth,
      |Real.log (sequence (n + 1)) - Real.log (sequence n) - Real.log multiplier| ≤ rate * sequence n) :
    |(depth : ℝ) * Real.log multiplier + Real.log (sequence 0)| ≤
      |Real.log (sequence depth)| + rate * sequence depth / (lower - 1) := by
  have h := finite_log_growth_error_bound sequence multiplier lower rate depth hlower hrate hstart hstep herror
  calc
    _ = |Real.log (sequence depth) -
        (Real.log (sequence depth) - Real.log (sequence 0) - (depth : ℝ) * Real.log multiplier)| := by congr 1; ring
    _ ≤ |Real.log (sequence depth)| +
        |Real.log (sequence depth) - Real.log (sequence 0) - (depth : ℝ) * Real.log multiplier| := abs_sub _ _
    _ ≤ _ := add_le_add le_rfl h

end
end Universality
