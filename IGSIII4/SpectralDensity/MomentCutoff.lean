import IGSIII4.SpectralDensity.CeilingGrowth
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem variance_remainder_vanishes (base : ℝ) (baseAboveOne : 1 < base) (constant : ℝ) :
    Tendsto (fun depth : ℕ =>
      1600 * constant ^ 2 * ((depth : ℝ) ^ 2 + 8 * (depth : ℝ) + 36) /
        (blockCount base depth : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have squareLimit := tendsto_pow_const_div_const_pow_of_one_lt 2 baseAboveOne
  have linearLimit := tendsto_pow_const_div_const_pow_of_one_lt 1 baseAboveOne
  have constantLimit := tendsto_pow_const_div_const_pow_of_one_lt 0 baseAboveOne
  have polynomialLimit := ((squareLimit.add (linearLimit.const_mul 8)).add
    (constantLimit.const_mul 36)).const_mul (1600 * constant ^ 2)
  simp only [mul_zero, zero_add] at polynomialLimit
  have normalizedLimit : Tendsto (fun depth : ℕ =>
      1600 * constant ^ 2 * ((depth : ℝ) ^ 2 + 8 * (depth : ℝ) + 36) / base ^ depth)
      atTop (𝓝 (0 : ℝ)) := by
    convert polynomialLimit using 1
    funext depth
    simp only [pow_one, pow_zero]
    ring
  apply squeeze_zero (fun depth => by positivity) (fun depth => ?_) normalizedLimit
  have powerPositive : 0 < base ^ depth := pow_pos (by linarith) _
  have countBound := (blockCount_bounds base baseAboveOne.le depth).1
  exact div_le_div_of_nonneg_left (by positivity) powerPositive countBound

theorem variance_remainder_eventually_small (base : ℝ) (baseAboveOne : 1 < base) (constant : ℝ) :
    ∀ᶠ depth : ℕ in atTop,
      1600 * constant ^ 2 * ((depth : ℝ) ^ 2 + 8 * (depth : ℝ) + 36) /
        (blockCount base depth : ℝ) < 4 :=
  (variance_remainder_vanishes base baseAboveOne constant).eventually (gt_mem_nhds (by norm_num))

theorem path_tail_remainder_eventually_small :
    ∀ᶠ depth : ℕ in atTop, 2 * ((depth : ℝ) + 8) * (69 / 70 : ℝ) ^ depth ≤ 1 := by
  have linearLimit := tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 69 / 70) (by norm_num : (69 / 70 : ℝ) < 1)
  have constantLimit := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 69 / 70) (by norm_num : (69 / 70 : ℝ) < 1)
  have limit := (linearLimit.add (constantLimit.const_mul 8)).const_mul 2
  simp only [mul_zero, zero_add] at limit
  have small := limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [small] with depth bound
  nlinarith [bound]

end
end IGSIII4.SpectralDensity
