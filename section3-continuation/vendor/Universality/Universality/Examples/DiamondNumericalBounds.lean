import Universality.Analysis.LogarithmRationalBounds
import Universality.Examples.DiamondClassical

namespace Universality
noncomputable section
set_option maxHeartbeats 1600000

theorem diamond_mass_thermal_rational_bounds :
    (37302885623 / 10000000000 : ℝ) ≤ 7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) ∧
    7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) ≤ 37302885625 / 10000000000 ∧
    (15278640449 / 10000000000 : ℝ) ≤ 6 - 2 * Real.sqrt 5 ∧
    6 - 2 * Real.sqrt 5 ≤ 15278640451 / 10000000000 := by
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsl : (22360679774997 / 10000000000000 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hsu : Real.sqrt 5 ≤ (22360679774998 / 10000000000000 : ℝ) := by nlinarith
  have hd : (0 : ℝ) ≤ 73 - 32 * Real.sqrt 5 := by linarith
  have ht0 := Real.sqrt_nonneg (73 - 32 * Real.sqrt 5)
  have ht2 := Real.sq_sqrt hd
  have htl : (120242451738 / 100000000000 : ℝ) ≤ Real.sqrt (73 - 32 * Real.sqrt 5) := by nlinarith
  have htu : Real.sqrt (73 - 32 * Real.sqrt 5) ≤ (120242451740 / 100000000000 : ℝ) := by nlinarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem diamond_logarithm_rational_bounds :
    (6931471805 / 10000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 6931471806 / 10000000000 ∧
    (4238707109 / 10000000000 : ℝ) ≤ Real.log (6 - 2 * Real.sqrt 5) ∧
    Real.log (6 - 2 * Real.sqrt 5) ≤ 4238707111 / 10000000000 ∧
    (698087677 / 10000000000 : ℝ) ≤ Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) ∧
    Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) ≤ 698087680 / 10000000000 := by
  have htwo := logarithm_rational_bounds 2 (by norm_num) 12
  have htwoL : (6931471805 / 10000000000 : ℝ) ≤ logarithmLowerBound 2 12 := by
    norm_num [logarithmLowerBound, Finset.sum_range_succ]
  have htwoU : logarithmUpperBound 2 12 ≤ (6931471806 / 10000000000 : ℝ) := by
    norm_num [logarithmUpperBound, logarithmLowerBound, Finset.sum_range_succ]
  have hthermalL := (logarithm_rational_bounds (15278640449 / 10000000000) (by norm_num) 8).1
  have hthermalU := (logarithm_rational_bounds (15278640451 / 10000000000) (by norm_num) 8).2
  have hthermalLCert : (4238707109 / 10000000000 : ℝ) ≤ logarithmLowerBound (15278640449 / 10000000000) 8 := by
    norm_num [logarithmLowerBound, Finset.sum_range_succ]
  have hthermalUCert : logarithmUpperBound (15278640451 / 10000000000) 8 ≤ (4238707111 / 10000000000 : ℝ) := by
    norm_num [logarithmUpperBound, logarithmLowerBound, Finset.sum_range_succ]
  have hratioL := (logarithm_rational_bounds (10723031028 / 10000000000) (by norm_num) 4).1
  have hratioU := (logarithm_rational_bounds (10723031029 / 10000000000) (by norm_num) 4).2
  have hratioLCert : (698087677 / 10000000000 : ℝ) ≤ logarithmLowerBound (10723031028 / 10000000000) 4 := by
    norm_num [logarithmLowerBound, Finset.sum_range_succ]
  have hratioUCert : logarithmUpperBound (10723031029 / 10000000000) 4 ≤ (698087680 / 10000000000 : ℝ) := by
    norm_num [logarithmUpperBound, logarithmLowerBound, Finset.sum_range_succ]
  obtain ⟨hmL, hmU, htL, htU⟩ := diamond_mass_thermal_rational_bounds
  have hm : 0 < 7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) := by linarith
  have hrL : (10723031028 / 10000000000 : ℝ) ≤ 4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) := by
    apply (le_div_iff₀ hm).mpr
    nlinarith
  have hrU : 4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) ≤ (10723031029 / 10000000000 : ℝ) := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  exact ⟨htwoL.trans htwo.1, htwo.2.trans htwoU,
    hthermalLCert.trans (hthermalL.trans (Real.log_le_log (by norm_num) htL)),
    (Real.log_le_log (by linarith) htU).trans (hthermalU.trans hthermalUCert),
    hratioLCert.trans (hratioL.trans (Real.log_le_log (by norm_num) hrL)),
    (Real.log_le_log (div_pos (by norm_num) hm) hrU).trans (hratioU.trans hratioUCert)⟩

end
end Universality
