import Universality.Analysis.RadiusPointExponentUpper

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology

theorem point_log_limit_ge_of_geometric_tail (probability tail : ℕ → ℝ)
    (htelescope : ∀ start length, (∑ i ∈ Finset.range length, probability (start + i)) =
      tail start - tail (start + length))
    (htailZero : Tendsto tail atTop (𝓝 0))
    (ratio lower : ℝ) (hratio : 0 < ratio) (hratio' : ratio < 1) (hlower : 0 < lower)
    (htailLower : ∀ᶠ n : ℕ in atTop, lower * ratio ^ n ≤ tail (2 ^ n))
    (exponent : ℝ) (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < probability radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (probability radius) / Real.log (radius : ℝ))
      atTop (𝓝 exponent)) : Real.log ratio / Real.log 2 - 1 ≤ exponent := by
  by_contra hfalse
  have hless : exponent < Real.log ratio / Real.log 2 - 1 := lt_of_not_ge hfalse
  obtain ⟨order, horderLower, horderUpper⟩ := exists_between hless
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : Real.log ratio < 0 := Real.log_neg hratio hratio'
  have horderNegative : order < 0 := by
    have : Real.log ratio / Real.log 2 < 0 := div_neg_of_neg_of_pos hlogRatio hlogTwo
    linarith
  let fast : ℝ := (2 : ℝ) ^ (1 + order)
  have hfastPositive : 0 < fast := Real.rpow_pos_of_pos (by norm_num) _
  have hfastSlow : fast < ratio := by
    change (2 : ℝ) ^ (1 + order) < ratio
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log hratio]
    apply Real.exp_lt_exp.mpr
    have hh := (lt_div_iff₀ hlogTwo).mp (show 1 + order < Real.log ratio / Real.log 2 by linarith)
    nlinarith
  have hpointUpper : ∀ᶠ radius : ℕ in atTop, probability radius ≤ (radius : ℝ) ^ order := by
    filter_upwards [hpositive, hlimit.eventually (gt_mem_nhds horderLower), eventually_gt_atTop 1]
      with radius hp hquotient hradius
    have hradiusReal : (1 : ℝ) < radius := by exact_mod_cast hradius
    have hlogPositive : 0 < Real.log (radius : ℝ) := Real.log_pos hradiusReal
    have hlogBound := (div_lt_iff₀ hlogPositive).mp hquotient
    rw [← Real.exp_log hp, Real.rpow_def_of_pos (zero_lt_one.trans hradiusReal)]
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp hpointUpper
  have hpowerTendsto : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))
  obtain ⟨start, hstart⟩ := eventually_atTop.mp (hpowerTendsto.eventually (eventually_ge_atTop threshold))
  have hdifference (n : ℕ) (hn : start ≤ n) : tail (2 ^ n) - tail (2 ^ (n + 1)) ≤ fast ^ n := by
    have hsum := htelescope (2 ^ n) (2 ^ n)
    rw [show 2 ^ n + 2 ^ n = 2 ^ (n + 1) by rw [pow_succ, Nat.mul_two]] at hsum
    rw [← hsum]
    calc
      _ ≤ ∑ _i ∈ Finset.range (2 ^ n), ((2 : ℝ) ^ n) ^ order := by
        apply Finset.sum_le_sum
        intro i _
        apply (hthreshold (2 ^ n + i) ((hstart n hn).trans (Nat.le_add_right _ _))).trans
        apply Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num) _)
          (by exact_mod_cast (Nat.le_add_right (2 ^ n) i)) horderNegative.le
      _ = fast ^ n := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [show (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) from (Real.rpow_natCast _ _).symm,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        dsimp only [fast]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have htailFast (n : ℕ) (hn : start ≤ n) : tail (2 ^ n) ≤ (1 / (1 - fast)) * fast ^ n := by
    have hh := geometric_tail_bound_of_differences (fun k => tail (2 ^ k)) (htailZero.comp hpowerTendsto)
      fast 1 hfastPositive.le (hfastSlow.trans hratio') n (fun k hk => by
        simpa only [one_mul] using hdifference k (hn.trans hk))
    simpa only [one_mul, one_div, div_eq_mul_inv, mul_comm] using hh
  have hcomparison : ∀ᶠ n : ℕ in atTop, lower * ratio ^ n ≤ (1 / (1 - fast)) * fast ^ n := by
    filter_upwards [htailLower, eventually_ge_atTop start] with n hn hstart
    exact hn.trans (htailFast n hstart)
  exact not_eventually_geometric_rate_comparison ratio fast lower (1 / (1 - fast))
    hfastPositive.le hratio hfastSlow hlower hcomparison

end
end Universality
