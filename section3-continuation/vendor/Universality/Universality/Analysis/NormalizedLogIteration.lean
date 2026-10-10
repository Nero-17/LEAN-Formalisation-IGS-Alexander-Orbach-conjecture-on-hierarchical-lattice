import Universality.Analysis.DiscountedIteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Universality
noncomputable section
set_option maxHeartbeats 0
open Filter
open scoped Topology

def normalizedLogLimit (sequence : ℕ → ℝ) (scale : ℝ) : ℝ :=
  Real.log (sequence 0) + ∑' n : ℕ, (1 / scale) ^ (n + 1) *
    (Real.log (sequence (n + 1)) - scale * Real.log (sequence n))

theorem normalized_log_telescoping (sequence : ℕ → ℝ) (scale : ℝ) (hscale : scale ≠ 0) (n : ℕ) :
    Real.log (sequence n) / scale ^ n = Real.log (sequence 0) +
      ∑ k ∈ Finset.range n, (1 / scale) ^ (k + 1) *
        (Real.log (sequence (k + 1)) - scale * Real.log (sequence k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, one_div_pow, pow_succ]
    field_simp
    <;> ring

theorem normalized_log_summable (sequence : ℕ → ℝ) (scale bound : ℝ)
    (hscale : 1 < scale)
    (hbound : ∀ n, |Real.log (sequence (n + 1)) - scale * Real.log (sequence n)| ≤ bound) :
    Summable (fun n : ℕ => (1 / scale) ^ (n + 1) *
      (Real.log (sequence (n + 1)) - scale * Real.log (sequence n))) := by
  have hd : 0 ≤ 1 / scale := one_div_nonneg.mpr (lt_trans zero_lt_one hscale).le
  have hd' : 1 / scale < 1 := (div_lt_one (lt_trans zero_lt_one hscale)).mpr hscale
  apply Summable.of_norm_bounded (g := fun n : ℕ => (1 / scale) ^ (n + 1) * bound)
    (((summable_geometric_of_lt_one hd hd').comp_injective
      (fun a b (h : a + 1 = b + 1) => Nat.add_right_cancel h)).mul_right bound)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _)]
  exact mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hd _)

theorem tendsto_normalized_log (sequence : ℕ → ℝ) (scale bound : ℝ)
    (hscale : 1 < scale)
    (hbound : ∀ n, |Real.log (sequence (n + 1)) - scale * Real.log (sequence n)| ≤ bound) :
    Tendsto (fun n : ℕ => Real.log (sequence n) / scale ^ n) atTop
      (𝓝 (normalizedLogLimit sequence scale)) := by
  simpa only [normalizedLogLimit, ← normalized_log_telescoping sequence scale
    (lt_trans zero_lt_one hscale).ne'] using
    (normalized_log_summable sequence scale bound hscale hbound).hasSum.tendsto_sum_nat.const_add
      (Real.log (sequence 0))

theorem normalizedLogLimit_error_bound (sequence : ℕ → ℝ) (scale bound : ℝ)
    (hscale : 1 < scale)
    (hbound : ∀ n, |Real.log (sequence (n + 1)) - scale * Real.log (sequence n)| ≤ bound) :
    |normalizedLogLimit sequence scale - Real.log (sequence 0)| ≤ bound / (scale - 1) := by
  have hpos := lt_trans zero_lt_one hscale
  have hd : 0 ≤ 1 / scale := one_div_nonneg.mpr hpos.le
  have hd' : 1 / scale < 1 := (div_lt_one hpos).mpr hscale
  have hseries : HasSum (fun n : ℕ => (1 / scale) ^ (n + 1) * bound) (bound / (scale - 1)) := by
    have h := (hasSum_geometric_of_lt_one hd hd').mul_left ((1 / scale) * bound)
    have hconstant : ((1 / scale) * bound) * (1 - 1 / scale)⁻¹ = bound / (scale - 1) := by
      field_simp
    rw [hconstant] at h
    exact h.congr_fun (fun n => by rw [pow_succ]; ring)
  simp only [normalizedLogLimit, add_sub_cancel_left, ← Real.norm_eq_abs]
  apply tsum_of_norm_bounded hseries
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hd _)]
  exact mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hd _)

theorem normalizedLogLimit_shift (sequence : ℕ → ℝ) (scale bound : ℝ)
    (hscale : 1 < scale)
    (hbound : ∀ n, |Real.log (sequence (n + 1)) - scale * Real.log (sequence n)| ≤ bound)
    (shift : ℕ) :
    normalizedLogLimit (fun n => sequence (n + shift)) scale = scale ^ shift * normalizedLogLimit sequence scale := by
  have hfirst := (tendsto_normalized_log sequence scale bound hscale hbound).comp (tendsto_add_atTop_nat shift)
  have hsecond := tendsto_normalized_log (fun n => sequence (n + shift)) scale bound hscale
    (fun n => by simpa only [Nat.add_right_comm n 1 shift] using hbound (n + shift))
  have hscaled := hfirst.const_mul (scale ^ shift)
  have hfunctions (n : ℕ) : scale ^ shift * (Real.log (sequence (n + shift)) / scale ^ (n + shift)) =
      Real.log (sequence (n + shift)) / scale ^ n := by
    rw [pow_add]
    field_simp
  simp only [Function.comp_def, hfunctions] at hscaled
  exact tendsto_nhds_unique hsecond hscaled

theorem normalizedLogLimit_neg (sequence : ℕ → ℝ) (scale bound : ℝ)
    (hscale : 1 < scale)
    (hbound : ∀ n, |Real.log (sequence (n + 1)) - scale * Real.log (sequence n)| ≤ bound)
    (hpositive : ∀ n, 0 < sequence n) (hzero : Tendsto sequence atTop (𝓝 0)) :
    normalizedLogLimit sequence scale < 0 := by
  obtain ⟨shift, hsmall⟩ := (hzero.eventually (gt_mem_nhds
    (Real.exp_pos (-bound / (scale - 1) - 1)))).exists
  have hlog : Real.log (sequence shift) < -bound / (scale - 1) - 1 := by
    simpa only [Real.log_exp] using Real.log_lt_log (hpositive shift) hsmall
  simp only [neg_div] at hlog
  have herror := normalizedLogLimit_error_bound (fun n => sequence (n + shift)) scale bound hscale
    (fun n => by simpa only [Nat.add_right_comm n 1 shift] using hbound (n + shift))
  rw [normalizedLogLimit_shift sequence scale bound hscale hbound shift] at herror
  simp only [zero_add] at herror
  have hupper := (abs_le.mp herror).2
  have hnegative : scale ^ shift * normalizedLogLimit sequence scale < 0 := by linarith
  by_contra hnonnegative
  exact (not_lt_of_ge (mul_nonneg (pow_nonneg (lt_trans zero_lt_one hscale).le shift)
    (le_of_not_gt hnonnegative))) hnegative

end
end Universality
