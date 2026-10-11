import Universality.Analysis.RadiusBlockProbability

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology

theorem no_point_log_limit_of_dyadic_spikes (probability : ℕ → ℝ)
    (hnonnegative : ∀ radius, 0 ≤ probability radius)
    (ratio lower upper : ℝ) (hratio : 0 < ratio) (hlower : 0 < lower) (hupper : 0 < upper)
    (hbounds : ∀ᶠ n : ℕ in atTop, lower * ratio ^ n ≤ probability (2 ^ n) ∧
      (∑ i ∈ Finset.range (2 ^ n), probability (2 ^ n + i)) ≤ upper * ratio ^ n) :
    ¬ ∃ exponent : ℝ, (∀ᶠ radius : ℕ in atTop, 0 < probability radius) ∧
      Tendsto (fun radius : ℕ => Real.log (probability radius) / Real.log (radius : ℝ))
        atTop (𝓝 exponent) := by
  rintro ⟨exponent, hpositive, hlimit⟩
  have hspikeBounds : ∀ᶠ n : ℕ in atTop, lower * ratio ^ n ≤ probability (2 ^ n) ∧
      probability (2 ^ n) ≤ upper * ratio ^ n := by
    filter_upwards [hbounds] with n hn
    refine ⟨hn.1, le_trans ?_ hn.2⟩
    have hh := Finset.single_le_sum
      (f := fun i => probability (2 ^ n + i)) (fun i _ => hnonnegative _)
      (Finset.mem_range.mpr (by positivity : 0 < 2 ^ n))
    simpa only [Nat.add_zero] using hh
  have hspike := logarithmic_growth_of_eventual_bounds (fun n => probability (2 ^ n))
    ratio lower upper hratio hlower hupper hspikeBounds
  have hscale := point_log_limit_along_dyadic_window probability exponent hlimit
    (fun n => 2 ^ n) (fun _ => le_rfl) (fun n => Nat.pow_le_pow_right (by decide) (by omega))
  have hexponent : exponent * Real.log 2 = Real.log ratio := tendsto_nhds_unique hscale hspike
  have hexists (n : ℕ) : ∃ radius : ℕ, 2 ^ n ≤ radius ∧ radius < 2 ^ (n + 1) ∧
      ((∑ i ∈ Finset.range (2 ^ n), probability (2 ^ n + i)) ≤ upper * ratio ^ n →
        probability radius ≤ upper * (ratio / 2) ^ n) := by
    by_cases hsum : (∑ i ∈ Finset.range (2 ^ n), probability (2 ^ n + i)) ≤ upper * ratio ^ n
    · obtain ⟨radius, hlo, hhi, hp⟩ := exists_small_point_in_block probability (2 ^ n) (2 ^ n)
        (by positivity) (upper * ratio ^ n) hsum
      refine ⟨radius, hlo, by simpa only [pow_succ, Nat.mul_two] using hhi, ?_⟩
      intro _
      simpa only [Nat.cast_pow, Nat.cast_ofNat, div_pow, mul_div_assoc] using hp
    · refine ⟨2 ^ n, le_rfl, ?_, fun hh => (hsum hh).elim⟩
      rw [pow_succ]
      have : 0 < (2 : ℕ) ^ n := by positivity
      omega
  choose index hlowerIndex hupperIndex hsmall using hexists
  have hindex := dyadic_window_index_tendsto index hlowerIndex
  have hselected := point_log_limit_along_dyadic_window probability exponent hlimit
    index hlowerIndex (fun n => (hupperIndex n).le)
  rw [hexponent] at hselected
  have hupperLimit : Tendsto
      (fun n : ℕ => Real.log upper / n + Real.log (ratio / 2)) atTop (𝓝 (Real.log (ratio / 2))) := by
    simpa only [zero_add] using (tendsto_const_div_atTop_nhds_zero_nat (Real.log upper)).add_const (Real.log (ratio / 2))
  have hle : ∀ᶠ n : ℕ in atTop, Real.log (probability (index n)) / n ≤
      Real.log upper / n + Real.log (ratio / 2) := by
    filter_upwards [hbounds, hindex.eventually hpositive, eventually_gt_atTop 0] with n hn hp hnpos
    have hlog := Real.log_le_log hp (hsmall n hn.2)
    rw [Real.log_mul hupper.ne' (pow_ne_zero _ (div_pos hratio (by norm_num)).ne'), Real.log_pow] at hlog
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).mpr
    field_simp
    nlinarith
  have hcontradiction := le_of_tendsto_of_tendsto hselected hupperLimit hle
  have hstrict : Real.log (ratio / 2) < Real.log ratio :=
    Real.log_lt_log (div_pos hratio (by norm_num)) (by linarith)
  exact (not_lt_of_ge hcontradiction) hstrict

end
end Universality
