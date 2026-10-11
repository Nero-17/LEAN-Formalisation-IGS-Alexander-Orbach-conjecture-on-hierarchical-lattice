import Universality.Analysis.RadiusBlockProbability
import Universality.Analysis.GeometricTailDifferences

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Filter
open scoped Topology

theorem point_log_limit_le_of_dyadic_block_bound (probability : ℕ → ℝ)
    (ratio upper : ℝ) (hratio : 0 < ratio) (hupper : 0 < upper)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      (∑ i ∈ Finset.range (2 ^ n), probability (2 ^ n + i)) ≤ upper * ratio ^ n)
    (exponent : ℝ) (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < probability radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (probability radius) / Real.log (radius : ℝ))
      atTop (𝓝 exponent)) : exponent * Real.log 2 ≤ Real.log (ratio / 2) := by
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
  have hupperLimit : Tendsto
      (fun n : ℕ => Real.log upper / n + Real.log (ratio / 2)) atTop (𝓝 (Real.log (ratio / 2))) := by
    simpa only [zero_add] using (tendsto_const_div_atTop_nhds_zero_nat (Real.log upper)).add_const (Real.log (ratio / 2))
  have hle : ∀ᶠ n : ℕ in atTop, Real.log (probability (index n)) / n ≤
      Real.log upper / n + Real.log (ratio / 2) := by
    filter_upwards [hbounds, hindex.eventually hpositive, eventually_gt_atTop 0] with n hn hp hnpos
    have hlog := Real.log_le_log hp (hsmall n hn)
    rw [Real.log_mul hupper.ne' (pow_ne_zero _ (div_pos hratio (by norm_num)).ne'), Real.log_pow] at hlog
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).mpr
    field_simp
    nlinarith
  exact le_of_tendsto_of_tendsto hselected hupperLimit hle

end
end Universality
