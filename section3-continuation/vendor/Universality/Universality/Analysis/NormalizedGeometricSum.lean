import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Universality
open Filter
open scoped Topology BigOperators

theorem normalized_geometric_sum_subcritical (radius rate : ℝ) (hradius : 1 < radius)
    (hrate : |rate| < radius) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), rate ^ k) / radius ^ n)
      atTop (𝓝 0) := by
  have hpositive : 0 < radius := lt_trans zero_lt_one hradius
  have hinverse : |radius⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hpositive)]
    exact inv_lt_one_of_one_lt₀ hradius
  have hinv := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hinverse
  by_cases hone : rate = 1
  · subst rate
    have hnat := tendsto_pow_const_div_const_pow_of_one_lt 1 hradius
    have hsum := hnat.add hinv
    simpa [Finset.sum_const, Nat.cast_add, Nat.cast_one, add_div, pow_one, one_div, inv_pow] using hsum
  · have hratio : |rate / radius| < 1 := by
      rw [abs_div, abs_of_pos hpositive]
      exact (div_lt_one hpositive).mpr hrate
    have hrateLimit := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
    have hlimit := ((hrateLimit.const_mul rate).sub hinv).div_const (rate - 1)
    have heq (n : ℕ) : (∑ k ∈ Finset.range (n + 1), rate ^ k) / radius ^ n =
        (rate * (rate / radius) ^ n - (radius⁻¹) ^ n) / (rate - 1) := by
      rw [(eq_div_iff (sub_ne_zero.mpr hone)).mpr (geom_sum_mul rate (n + 1))]
      rw [pow_succ, div_pow, inv_pow]
      field_simp
    simpa only [heq, mul_zero, sub_zero, zero_div] using hlimit

theorem normalized_geometric_sum_supercritical (radius : ℝ) (hradius : 1 < radius) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), radius ^ k) / radius ^ n)
      atTop (𝓝 (radius / (radius - 1))) := by
  have hpositive : 0 < radius := lt_trans zero_lt_one hradius
  have hinv := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (show |radius⁻¹| < 1 by
      rw [abs_of_pos (inv_pos.mpr hpositive)]
      exact inv_lt_one_of_one_lt₀ hradius)
  have heq (n : ℕ) : (∑ k ∈ Finset.range (n + 1), radius ^ k) / radius ^ n =
      (radius - (radius⁻¹) ^ n) / (radius - 1) := by
    rw [(eq_div_iff (sub_pos.mpr hradius).ne').mpr (geom_sum_mul radius (n + 1))]
    rw [pow_succ, inv_pow]
    field_simp
  simpa only [heq, sub_zero] using (tendsto_const_nhds.sub hinv).div_const (radius - 1)

end Universality
