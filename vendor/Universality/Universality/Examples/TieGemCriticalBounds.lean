import Universality.Examples.TieGemClassical
import Universality.Percolation.ClassicalCriticalPoint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section

/-- The actual gem reliability fixed point satisfies this quartic. -/
theorem gem_interior_fixed_quartic (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) : p ^ 4 + p ^ 3 = 1 := by
  have hzero : p * (1 - p) * (p ^ 4 + p ^ 3 - 1) = 0 := by
    calc
      _ = gemRule.network.reliability p - p := by rw [gem_reliability]; ring
      _ = 0 := sub_eq_zero.mpr hfixed
  have hh := (mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero hp.ne' (sub_pos.mpr hp').ne')
  linarith

/-- Exact rational isolation, stronger than four-decimal rounding. -/
theorem gem_critical_point_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (8191725 : ℝ) / 10000000 < p ∧ p < (8191726 : ℝ) / 10000000 := by
  have hquartic := gem_interior_fixed_quartic p hp hp' hfixed
  constructor
  · by_contra hh
    have hle := le_of_not_gt hh
    have h3 := pow_le_pow_left₀ hp.le hle 3
    have h4 := pow_le_pow_left₀ hp.le hle 4
    norm_num at h3 h4
    linarith
  · by_contra hh
    have hle := le_of_not_gt hh
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8191726 / 10000000) hle 3
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8191726 / 10000000) hle 4
    norm_num at h3 h4
    linarith

/-- The squared gem fixed point rounds to the displayed tie critical parameter. -/
theorem tie_critical_point_bounds_of_gem (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (67095 : ℝ) / 100000 < p ^ 2 ∧ p ^ 2 < (67105 : ℝ) / 100000 := by
  obtain ⟨hlower, hupper⟩ := gem_critical_point_rational_bounds p hp hp' hfixed
  have hl := pow_lt_pow_left₀ hlower (by norm_num : (0 : ℝ) ≤ 8191725 / 10000000)
    (by omega : (2 : ℕ) ≠ 0)
  have hu := pow_lt_pow_left₀ hupper hp.le (by omega : (2 : ℕ) ≠ 0)
  norm_num at hl hu
  constructor <;> linarith

/-- The bound concerns the actual tie critical fixed point. -/
theorem tie_critical_point_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : tieRule.network.reliability p = p) :
    (67095 : ℝ) / 100000 < p ∧ p < (67105 : ℝ) / 100000 := by
  obtain ⟨q, hq, hq', hqfixed⟩ := gemRule_classical.exists_interior_fixed_point
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have hq2' : q ^ 2 < 1 := by nlinarith
  have heq := tieRule.network.interior_fixed_point_unique p (q ^ 2)
    hp hp' hq2 hq2' hfixed (tie_gem_fixed_point q hqfixed).1 tieRule_classical.scale
  rw [heq]
  exact tie_critical_point_bounds_of_gem q hq hq' hqfixed

end
end Universality
