import Universality.Analysis.PowerResponseExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem wheatstone_response_order_bounds :
    0 < Real.log 5 / Real.log (13 / 8) - 3 ∧ Real.log 5 / Real.log (13 / 8) - 3 < 1 := by
  have hlog : 0 < Real.log (13 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hthree : 3 * Real.log (13 / 8 : ℝ) < Real.log 5 := by
    have h := Real.log_lt_log (show (0 : ℝ) < (13 / 8) ^ 3 by norm_num)
      (show (13 / 8 : ℝ) ^ 3 < 5 by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hfour : Real.log 5 < 4 * Real.log (13 / 8 : ℝ) := by
    have h := Real.log_lt_log (show (0 : ℝ) < 5 by norm_num)
      (show (5 : ℝ) < (13 / 8) ^ 4 by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  constructor
  · have := (lt_div_iff₀ hlog).mpr hthree
    linarith
  · have := (div_lt_iff₀ hlog).mpr hfour
    linarith

theorem wheatstone_normalized_coefficient_lt_one (order : ℝ)
    (horder : order < Real.log 5 / Real.log (13 / 8) - 3) :
    (13 / 8 : ℝ) ^ 3 / 5 * (13 / 8 : ℝ) ^ order < 1 := by
  have hlog : 0 < Real.log (13 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hpower : (13 / 8 : ℝ) ^ ((3 : ℝ) + order) < 5 := by
    apply (Real.rpow_lt_iff_lt_log (by norm_num) (by norm_num)).mpr
    apply (lt_div_iff₀ hlog).mp
    linarith
  have hid : (13 / 8 : ℝ) ^ ((3 : ℝ) + order) = (13 / 8 : ℝ) ^ 3 * (13 / 8 : ℝ) ^ order := by
    rw [Real.rpow_add (by norm_num)]
    congr 1
    exact Real.rpow_natCast (13 / 8) 3
  rw [hid] at hpower
  nlinarith

theorem wheatstone_normalized_coefficient_gt_one (order : ℝ)
    (horder : Real.log 5 / Real.log (13 / 8) - 3 < order) :
    1 < (13 / 8 : ℝ) ^ 3 / 5 * (13 / 8 : ℝ) ^ order := by
  have hlog : 0 < Real.log (13 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hpower : 5 < (13 / 8 : ℝ) ^ ((3 : ℝ) + order) := by
    apply (Real.lt_rpow_iff_log_lt (by norm_num) (by norm_num)).mpr
    apply (div_lt_iff₀ hlog).mp
    linarith
  have hid : (13 / 8 : ℝ) ^ ((3 : ℝ) + order) = (13 / 8 : ℝ) ^ 3 * (13 / 8 : ℝ) ^ order := by
    rw [Real.rpow_add (by norm_num)]
    congr 1
    exact Real.rpow_natCast (13 / 8) 3
  rw [hid] at hpower
  nlinarith

/-- Power barriers with exponents arbitrarily close on both sides determine
the logarithmic exponent, without asserting a nonzero periodic amplitude. -/
theorem logarithmic_order_of_power_barriers {space : Type*} (filter : Filter space)
    (response deviation : space → ℝ) (exponent : ℝ) (hexponent : 0 < exponent) (hexponentOne : exponent < 1)
    (hdeviation : Tendsto (fun point => Real.log (deviation point)) filter atBot)
    (hpositive : ∀ᶠ point in filter, 0 < deviation point ∧ 0 < response point)
    (hupper : ∀ order : ℝ, 0 < order → order < exponent →
      ∀ᶠ point in filter, response point ≤ deviation point ^ order)
    (hlower : ∀ order : ℝ, exponent < order → order < 1 →
      ∃ coefficient : ℝ, 0 < coefficient ∧
        ∀ᶠ point in filter, coefficient * deviation point ^ order ≤ response point) :
    Tendsto (fun point => Real.log (response point) / Real.log (deviation point)) filter (𝓝 exponent) := by
  apply tendsto_order.mpr
  constructor
  · intro lower hlowerExponent
    obtain ⟨order, horderLower, horderUpper⟩ := exists_between (max_lt hexponent hlowerExponent)
    have horderPositive : 0 < order := (le_max_left (0 : ℝ) lower).trans_lt horderLower
    have horderAbove : lower < order := (le_max_right (0 : ℝ) lower).trans_lt horderLower
    filter_upwards [hpositive, hupper order horderPositive horderUpper,
      hdeviation.eventually (eventually_lt_atBot (0 : ℝ))] with point hp hu hn
    have hlog : Real.log (response point) ≤ order * Real.log (deviation point) := by
      simpa only [Real.log_rpow hp.1] using Real.log_le_log hp.2 hu
    exact horderAbove.trans_le ((le_div_iff_of_neg hn).mpr hlog)
  · intro upper hupperExponent
    obtain ⟨order, horderLower, horderUpper⟩ := exists_between (lt_min hexponentOne hupperExponent)
    have horderOne : order < 1 := horderUpper.trans_le (min_le_left _ _)
    have horderBelow : order < upper := horderUpper.trans_le (min_le_right _ _)
    obtain ⟨coefficient, hcoefficient, hlowerBound⟩ := hlower order horderLower horderOne
    have herror : Tendsto (fun point => order + Real.log coefficient / Real.log (deviation point))
        filter (𝓝 order) := by
      have h := ((tendsto_const_nhds : Tendsto (fun _ : space => Real.log coefficient) filter
        (𝓝 (Real.log coefficient))).mul (tendsto_inv_atBot_zero.comp hdeviation)).const_add order
      simpa only [div_eq_mul_inv, mul_zero, add_zero, Function.comp_def] using h
    filter_upwards [hpositive, hlowerBound,
      hdeviation.eventually (eventually_lt_atBot (0 : ℝ)),
      herror.eventually (gt_mem_nhds horderBelow)] with point hp hl hn he
    have hlog : Real.log coefficient + order * Real.log (deviation point) ≤ Real.log (response point) := by
      have h := Real.log_le_log (mul_pos hcoefficient (Real.rpow_pos_of_pos hp.1 order)) hl
      simpa only [Real.log_mul hcoefficient.ne' (Real.rpow_pos_of_pos hp.1 order).ne',
        Real.log_rpow hp.1] using h
    have hquotient : Real.log (response point) / Real.log (deviation point) ≤
        order + Real.log coefficient / Real.log (deviation point) := by
      apply (div_le_iff_of_neg hn).mpr
      have hid : (order + Real.log coefficient / Real.log (deviation point)) * Real.log (deviation point) =
          Real.log coefficient + order * Real.log (deviation point) := by
        field_simp [hn.ne]
        ring
      rwa [hid]
    exact hquotient.trans_lt he

end
end Universality
