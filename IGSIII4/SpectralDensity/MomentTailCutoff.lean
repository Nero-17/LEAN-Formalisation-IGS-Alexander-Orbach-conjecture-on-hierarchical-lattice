import IGSIII4.SpectralDensity.MomentCutoff

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem path_tail_remainder_relative_eventually_small (constant : ℝ) :
    ∀ᶠ depth : ℕ in atTop,
      4 * constant * (depth : ℝ) * (69 / 70 : ℝ) ^ depth < 1 := by
  have linearLimit := tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 69 / 70) (by norm_num : (69 / 70 : ℝ) < 1)
  have limit := linearLimit.const_mul (4 * constant)
  simp only [mul_zero] at limit
  have small := limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [small] with depth bound
  nlinarith [bound]

end
end IGSIII4.SpectralDensity
