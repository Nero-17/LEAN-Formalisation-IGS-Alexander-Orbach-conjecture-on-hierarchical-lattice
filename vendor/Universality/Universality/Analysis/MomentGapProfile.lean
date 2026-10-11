import Universality.Analysis.MomentGapAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Universality
noncomputable section
open Filter

/-- Express the ratio exponent directly in the logarithms of the growth
and volume factors. -/
theorem logarithmic_power_gap_identity (growth volume multiplier : ℝ)
    (hgrowth : 0 < growth) (hvolume : 0 < volume) (order : ℕ) :
    (max (Real.log (growth ^ (order + 2) / volume)) 0 -
      max (Real.log (growth ^ (order + 1) / volume)) 0) / Real.log multiplier =
    (max (((order + 2 : ℕ) : ℝ) * Real.log growth - Real.log volume) 0 -
      max (((order + 1 : ℕ) : ℝ) * Real.log growth - Real.log volume) 0) /
        Real.log multiplier := by
  rw [Real.log_div (pow_pos hgrowth _).ne' hvolume.ne',
    Real.log_div (pow_pos hgrowth _).ne' hvolume.ne', Real.log_pow, Real.log_pow]

/-- The full positive-order common-gap criterion, including equality. -/
theorem all_logarithmic_power_gaps_eq_iff (growth volume multiplier : ℝ)
    (hgrowth : 1 < growth) (hvolume : 0 < volume) (hmultiplier : 1 < multiplier) :
    (∀ order : ℕ, 1 ≤ order →
      (max (Real.log (growth ^ (order + 2) / volume)) 0 -
        max (Real.log (growth ^ (order + 1) / volume)) 0) / Real.log multiplier =
          Real.log growth / Real.log multiplier) ↔ volume ≤ growth ^ 2 := by
  have hlog : Real.log multiplier ≠ 0 := (Real.log_pos hmultiplier).ne'
  simp_rw [logarithmic_power_gap_identity growth volume multiplier
    (zero_lt_one.trans hgrowth) hvolume, div_left_inj' hlog]
  rw [all_positive_part_gaps_eq_iff (Real.log growth) (Real.log volume) (Real.log_pos hgrowth)]
  have hh := Real.log_le_log_iff hvolume (pow_pos (zero_lt_one.trans hgrowth) 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

/-- Every sufficiently high ratio has the common logarithmic exponent. -/
theorem eventually_logarithmic_power_gaps_eq (growth volume multiplier : ℝ)
    (hgrowth : 1 < growth) (hvolume : 0 < volume) :
    ∀ᶠ order : ℕ in atTop,
      (max (Real.log (growth ^ (order + 2) / volume)) 0 -
        max (Real.log (growth ^ (order + 1) / volume)) 0) / Real.log multiplier =
          Real.log growth / Real.log multiplier := by
  filter_upwards [eventually_positive_part_gaps_eq (Real.log growth) (Real.log volume)
    (Real.log_pos hgrowth)] with order horder
  rw [logarithmic_power_gap_identity growth volume multiplier
    (zero_lt_one.trans hgrowth) hvolume, horder]

end
end Universality
