import Universality.Analysis.BoundedLogError
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section

theorem log_error_of_geometric_comparison (response base lower upper : ℝ) (depth : ℕ)
    (hbase : 0 < base) (hlower : 0 < lower) (hupper : 0 < upper)
    (hlowerBound : lower * base ^ depth ≤ response)
    (hupperBound : response ≤ upper * base ^ depth) :
    |Real.log response - (depth : ℝ) * Real.log base| ≤ |Real.log lower| + |Real.log upper| := by
  have hresponse : 0 < response := (mul_pos hlower (pow_pos hbase _)).trans_le hlowerBound
  have hleft := Real.log_le_log (mul_pos hlower (pow_pos hbase _)) hlowerBound
  have hright := Real.log_le_log hresponse hupperBound
  rw [Real.log_mul hlower.ne' (pow_ne_zero _ hbase.ne'), Real.log_pow] at hleft
  rw [Real.log_mul hupper.ne' (pow_ne_zero _ hbase.ne'), Real.log_pow] at hright
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log lower), abs_nonneg (Real.log upper)],
    by linarith [le_abs_self (Real.log upper), abs_nonneg (Real.log lower)]⟩

theorem stopped_geometric_log_error (response base multiplier deviation lower upper bound : ℝ)
    (depth : ℕ) (hbase : 0 < base) (hmultiplier : Real.log multiplier ≠ 0)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hlowerBound : lower * base ^ depth ≤ response)
    (hupperBound : response ≤ upper * base ^ depth)
    (hescape : |(depth : ℝ) * Real.log multiplier + Real.log deviation| ≤ bound) :
    |Real.log response - (-Real.log base / Real.log multiplier) * Real.log deviation| ≤
      |Real.log lower| + |Real.log upper| + |Real.log base / Real.log multiplier| * bound := by
  have hmass := log_error_of_geometric_comparison response base lower upper depth hbase hlower hupper hlowerBound hupperBound
  have hidentity : Real.log response - (-Real.log base / Real.log multiplier) * Real.log deviation =
      (Real.log response - (depth : ℝ) * Real.log base) +
        (Real.log base / Real.log multiplier) * ((depth : ℝ) * Real.log multiplier + Real.log deviation) := by
    field_simp [hmultiplier]
    <;> ring
  rw [hidentity]
  calc
    _ ≤ |Real.log response - (depth : ℝ) * Real.log base| +
        |(Real.log base / Real.log multiplier) * ((depth : ℝ) * Real.log multiplier + Real.log deviation)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add hmass (mul_le_mul_of_nonneg_left hescape (abs_nonneg _))

end
end Universality
