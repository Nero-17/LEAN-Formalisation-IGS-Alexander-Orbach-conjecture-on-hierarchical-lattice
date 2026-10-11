import Universality.Analysis.StoppedGeometricLogBound
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality
noncomputable section
set_option maxHeartbeats 500000
open Filter
open scoped Topology

theorem sum_successive_differences (sequence : ℕ → ℝ) (start length : ℕ) :
    (∑ i ∈ Finset.range length, (sequence (start + i) - sequence (start + i + 1))) =
      sequence start - sequence (start + length) := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_assoc]
    ring

theorem geometric_tail_bound_of_differences (sequence : ℕ → ℝ)
    (hzero : Tendsto sequence atTop (𝓝 0)) (ratio constant : ℝ)
    (hratio : 0 ≤ ratio) (hratio' : ratio < 1) (start : ℕ)
    (hbound : ∀ n, start ≤ n → sequence n - sequence (n + 1) ≤ constant * ratio ^ n) :
    sequence start ≤ constant * ratio ^ start / (1 - ratio) := by
  have hfinite (length : ℕ) : sequence start - sequence (start + length) ≤
      ∑ i ∈ Finset.range length, (constant * ratio ^ start) * ratio ^ i := by
    rw [← sum_successive_differences sequence start length]
    apply Finset.sum_le_sum
    intro i _
    simpa only [pow_add, mul_assoc] using hbound (start + i) (Nat.le_add_right _ _)
  have hleft : Tendsto (fun length : ℕ => sequence start - sequence (start + length)) atTop (𝓝 (sequence start)) := by
    have hh : Tendsto (fun length : ℕ => sequence (start + length)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.add_comm start] using hzero.comp (tendsto_add_atTop_nat start)
    simpa only [sub_zero] using (tendsto_const_nhds (x := sequence start)).sub hh
  have hsum := ((summable_geometric_of_lt_one hratio hratio').mul_left (constant * ratio ^ start)).hasSum.tendsto_sum_nat
  have hle := le_of_tendsto_of_tendsto hleft hsum (Eventually.of_forall hfinite)
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one hratio hratio', div_eq_mul_inv] using hle

theorem not_eventually_geometric_rate_comparison (slow fast lower upper : ℝ)
    (hfast : 0 ≤ fast) (hslow : 0 < slow) (horder : fast < slow) (hlower : 0 < lower) :
    ¬ ∀ᶠ n : ℕ in atTop, lower * slow ^ n ≤ upper * fast ^ n := by
  intro hcomparison
  have hquotient : ∀ᶠ n : ℕ in atTop, lower ≤ upper * (fast / slow) ^ n := by
    filter_upwards [hcomparison] with n hn
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos hslow n)).mpr hn
  have hzero := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hfast hslow.le)
    ((div_lt_one hslow).mpr horder)).const_mul upper
  simp only [mul_zero] at hzero
  have hle := le_of_tendsto_of_tendsto (tendsto_const_nhds (x := lower)) hzero hquotient
  exact (not_le_of_gt hlower) hle

end
end Universality
