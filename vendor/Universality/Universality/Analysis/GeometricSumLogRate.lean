import Universality.Matrix.ColumnGrowth
import Mathlib.Algebra.Field.GeomSum

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem geometric_sum_from_one_bounds_above_one (ratio : ℝ) (hratio : 1 < ratio)
    (depth : ℕ) (hdepth : 1 ≤ depth) :
    ratio ^ depth ≤ (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) ∧
      (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) ≤
        (ratio / (ratio - 1)) * ratio ^ depth := by
  have hpos : 0 < ratio := zero_lt_one.trans hratio
  constructor
  · have hh := Finset.single_le_sum (s := Finset.range depth)
      (f := fun n => ratio ^ (n + 1)) (fun n _ => (pow_pos hpos _).le)
      (Finset.mem_range.mpr (show depth - 1 < depth by omega))
    simpa only [show depth - 1 + 1 = depth by omega] using hh
  · have heq : (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) =
        ratio * ((ratio ^ depth - 1) / (ratio - 1)) := by
      simp only [pow_succ', ← Finset.mul_sum, geom_sum_eq hratio.ne']
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (show ratio ^ depth - 1 ≤ ratio ^ depth by linarith)
        (sub_pos.mpr hratio).le) hpos.le
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using hh

theorem geometric_sum_from_one_bounds_below_one (ratio : ℝ) (hratio : 0 < ratio)
    (hratioOne : ratio < 1) (depth : ℕ) (hdepth : 1 ≤ depth) :
    ratio ≤ (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) ∧
      (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) ≤ ratio / (1 - ratio) := by
  constructor
  · have hh := Finset.single_le_sum (s := Finset.range depth)
      (f := fun n => ratio ^ (n + 1)) (fun n _ => (pow_pos hratio _).le)
      (Finset.mem_range.mpr (show 0 < depth by omega))
    simpa only [zero_add, pow_one] using hh
  · have hs := (summable_geometric_of_lt_one hratio.le hratioOne).mul_left ratio
    have hh := hs.sum_le_tsum (Finset.range depth) (fun n _ => mul_nonneg hratio.le (pow_nonneg hratio.le _))
    rw [tsum_mul_left, tsum_geometric_of_lt_one hratio.le hratioOne] at hh
    simpa only [← pow_succ', div_eq_mul_inv] using hh

/-- The logarithmic growth per generation of the stopped geometric sum
has all three regimes, including the linear sum when the ratio is one. -/
theorem geometric_sum_log_rate (ratio : ℝ) (hratio : 0 < ratio) :
    Tendsto (fun depth : ℕ => Real.log (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) / depth)
      atTop (𝓝 (max (Real.log ratio) 0)) := by
  rcases lt_trichotomy ratio 1 with hbelow | heq | habove
  · rw [max_eq_right (Real.log_nonpos hratio.le hbelow.le)]
    have hh := logarithmic_growth_of_eventual_bounds
      (fun depth => ∑ n ∈ Finset.range depth, ratio ^ (n + 1)) 1 ratio (ratio / (1 - ratio))
      zero_lt_one hratio (div_pos hratio (sub_pos.mpr hbelow))
      ((eventually_ge_atTop 1).mono (fun n hn => by
        simpa only [one_pow, mul_one] using geometric_sum_from_one_bounds_below_one ratio hratio hbelow n hn))
    simpa only [Real.log_one] using hh
  · subst ratio
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Real.log_one, max_self]
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using hh
  · rw [max_eq_left (Real.log_pos habove).le]
    apply logarithmic_growth_of_eventual_bounds _ ratio 1 (ratio / (ratio - 1))
      hratio zero_lt_one (div_pos hratio (sub_pos.mpr habove))
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [one_mul] using geometric_sum_from_one_bounds_above_one ratio habove n hn

end
end Universality
