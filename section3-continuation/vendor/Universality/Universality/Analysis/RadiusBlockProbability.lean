import Universality.Matrix.ColumnGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Universality
noncomputable section
set_option maxHeartbeats 500000
open Filter
open scoped Topology

theorem exists_small_point_in_block (probability : ℕ → ℝ) (start length : ℕ)
    (hlength : 0 < length) (bound : ℝ)
    (hsum : (∑ i ∈ Finset.range length, probability (start + i)) ≤ bound) :
    ∃ radius : ℕ, start ≤ radius ∧ radius < start + length ∧ probability radius ≤ bound / length := by
  have hcard : (∑ _i ∈ Finset.range length, bound / (length : ℝ)) = bound := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [ne_of_gt (show (0 : ℝ) < length by exact_mod_cast hlength)]
  obtain ⟨index, hindex, hpoint⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hlength)) (hsum.trans_eq hcard.symm)
  exact ⟨start + index, by omega, by have := Finset.mem_range.mp hindex; omega, hpoint⟩

theorem dyadic_window_index_tendsto (index : ℕ → ℕ)
    (hlower : ∀ n, 2 ^ n ≤ index n) : Tendsto index atTop atTop :=
  tendsto_atTop_mono hlower (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))

theorem dyadic_window_log_growth (index : ℕ → ℕ)
    (hlower : ∀ n, 2 ^ n ≤ index n) (hupper : ∀ n, index n ≤ 2 ^ (n + 1)) :
    Tendsto (fun n : ℕ => Real.log (index n : ℝ) / n) atTop (𝓝 (Real.log 2)) := by
  have hb : ∀ᶠ n : ℕ in atTop, (1 : ℝ) * (2 : ℝ) ^ n ≤ (index n : ℝ) ∧
      (index n : ℝ) ≤ 2 * (2 : ℝ) ^ n := by
    apply Eventually.of_forall
    intro n
    constructor
    · simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (show ((2 ^ n : ℕ) : ℝ) ≤ (index n : ℝ) by exact_mod_cast hlower n)
    · have hh : (index n : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hupper n
      simpa only [pow_succ', Nat.cast_ofNat] using hh
  exact logarithmic_growth_of_eventual_bounds (fun n => (index n : ℝ)) 2 1 2
    (by norm_num) (by norm_num) (by norm_num) hb

theorem point_log_limit_along_dyadic_window (probability : ℕ → ℝ) (exponent : ℝ)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (probability radius) / Real.log (radius : ℝ))
      atTop (𝓝 exponent))
    (index : ℕ → ℕ) (hlower : ∀ n, 2 ^ n ≤ index n) (hupper : ∀ n, index n ≤ 2 ^ (n + 1)) :
    Tendsto (fun n : ℕ => Real.log (probability (index n)) / n) atTop (𝓝 (exponent * Real.log 2)) := by
  have hindex := dyadic_window_index_tendsto index hlower
  have hproduct := (hlimit.comp hindex).mul (dyadic_window_log_growth index hlower hupper)
  apply hproduct.congr'
  filter_upwards [hindex.eventually (eventually_gt_atTop 1)] with n hn
  have hlog : Real.log (index n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  dsimp only [Function.comp_def]
  field_simp [hlog]

end
end Universality

