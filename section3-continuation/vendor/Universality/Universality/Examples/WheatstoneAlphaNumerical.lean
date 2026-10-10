import Universality.Examples.DiamondNumericalBounds

namespace Universality
noncomputable section
set_option maxHeartbeats 1600000

theorem wheatstone_alpha_logarithm_rational_bounds :
    (16094379123 / 10000000000 : ℝ) ≤ Real.log 5 ∧
      Real.log 5 ≤ 16094379126 / 10000000000 ∧
    (4855078157 / 10000000000 : ℝ) ≤ Real.log (13 / 8) ∧
      Real.log (13 / 8) ≤ 4855078159 / 10000000000 := by
  have hquarter := logarithm_rational_bounds (5/4) (by norm_num) 6
  have hquarterL : (2231435513 / 10000000000 : ℝ) ≤ logarithmLowerBound (5/4) 6 := by
    norm_num [logarithmLowerBound, Finset.sum_range_succ]
  have hquarterU : logarithmUpperBound (5/4) 6 ≤ (2231435514 / 10000000000 : ℝ) := by
    norm_num [logarithmUpperBound, logarithmLowerBound, Finset.sum_range_succ]
  have hthermal := logarithm_rational_bounds (13/8) (by norm_num) 8
  have hthermalL : (4855078157 / 10000000000 : ℝ) ≤ logarithmLowerBound (13/8) 8 := by
    norm_num [logarithmLowerBound, Finset.sum_range_succ]
  have hthermalU : logarithmUpperBound (13/8) 8 ≤ (4855078159 / 10000000000 : ℝ) := by
    norm_num [logarithmUpperBound, logarithmLowerBound, Finset.sum_range_succ]
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hfive : Real.log (5 : ℝ) = 2 * Real.log 2 + Real.log (5/4) := by
    rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0), hfour]
    ring
  have h2L := diamond_logarithm_rational_bounds.1
  have h2U := diamond_logarithm_rational_bounds.2.1
  have hqL := hquarterL.trans hquarter.1
  have hqU := hquarter.2.trans hquarterU
  refine ⟨?_, ?_, hthermalL.trans hthermal.1, hthermal.2.trans hthermalU⟩
  · rw [hfive]
    linarith
  · rw [hfive]
    linarith

/-- An explicit rounding interval for the original full-response alpha. -/
theorem wheatstone_raw_alpha_decimal_bounds :
    (-131505 / 100000 : ℝ) ≤ 2 - Real.log 5 / Real.log (13/8) ∧
      2 - Real.log 5 / Real.log (13/8) ≤ (-131495 / 100000 : ℝ) := by
  obtain ⟨h5L, h5U, htL, htU⟩ := wheatstone_alpha_logarithm_rational_bounds
  have ht : 0 < Real.log (13/8 : ℝ) := by linarith
  constructor
  · have hh := (div_le_iff₀ ht).mpr (show Real.log (5 : ℝ) ≤
        (2 + 131505 / 100000) * Real.log (13/8) by nlinarith)
    linarith
  · have hh := (le_div_iff₀ ht).mpr (show
        (2 + 131495 / 100000) * Real.log (13/8 : ℝ) ≤ Real.log 5 by nlinarith)
    linarith

end
end Universality
