import Universality.Analysis.RadiusPointExponentLower

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology

theorem point_log_limit_eq_of_tail_power_bounds (probability tail : ℕ → ℝ)
    (htelescope : ∀ start length, (∑ i ∈ Finset.range length, probability (start + i)) =
      tail start - tail (start + length))
    (htailNonneg : ∀ radius, 0 ≤ tail radius)
    (htailZero : Tendsto tail atTop (𝓝 0))
    (tailExponent lower upper : ℝ) (hnegative : tailExponent < 0)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (htail : ∀ᶠ radius : ℕ in atTop,
      lower * (radius : ℝ) ^ tailExponent ≤ tail radius ∧
      tail radius ≤ upper * (radius : ℝ) ^ tailExponent)
    (exponent : ℝ) (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < probability radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (probability radius) / Real.log (radius : ℝ))
      atTop (𝓝 exponent)) : exponent = tailExponent - 1 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratioPositive : 0 < (2 : ℝ) ^ tailExponent := Real.rpow_pos_of_pos (by norm_num) _
  have hratioLt : (2 : ℝ) ^ tailExponent < 1 := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg hlogTwo hnegative)
  have hpowerTendsto : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
  have hdyadic : ∀ᶠ n : ℕ in atTop,
      lower * ((2 : ℝ) ^ tailExponent) ^ n ≤ tail (2 ^ n) ∧
      tail (2 ^ n) ≤ upper * ((2 : ℝ) ^ tailExponent) ^ n := by
    filter_upwards [hpowerTendsto.eventually htail] with n hn
    have hpow : (((2 ^ n : ℕ) : ℝ) ^ tailExponent) = ((2 : ℝ) ^ tailExponent) ^ n := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    simpa only [hpow] using hn
  have hblock : ∀ᶠ n : ℕ in atTop,
      (∑ i ∈ Finset.range (2 ^ n), probability (2 ^ n + i)) ≤ upper * ((2 : ℝ) ^ tailExponent) ^ n := by
    filter_upwards [hdyadic] with n hn
    rw [htelescope]
    exact (sub_le_self _ (htailNonneg _)).trans hn.2
  have hlow := point_log_limit_ge_of_geometric_tail probability tail htelescope htailZero
    ((2 : ℝ) ^ tailExponent) lower hratioPositive hratioLt hlower
    (hdyadic.mono (fun _ hn => hn.1)) exponent hpositive hlimit
  have hupp := point_log_limit_le_of_dyadic_block_bound probability
    ((2 : ℝ) ^ tailExponent) upper hratioPositive hupper hblock exponent hpositive hlimit
  have hlog : Real.log ((2 : ℝ) ^ tailExponent) = Real.log 2 * tailExponent := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.log_exp]
  rw [hlog] at hlow
  have hquotient : Real.log 2 * tailExponent / Real.log 2 = tailExponent := by field_simp [hlogTwo.ne']
  rw [hquotient] at hlow
  rw [Real.log_div hratioPositive.ne' (by norm_num), hlog] at hupp
  have : exponent ≤ tailExponent - 1 := by
    nlinarith
  exact le_antisymm this hlow

end
end Universality


