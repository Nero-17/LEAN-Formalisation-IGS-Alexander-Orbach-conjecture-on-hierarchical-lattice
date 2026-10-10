import Universality.Arithmetic.Commensurability
import Universality.Arithmetic.GelfondSchneider

/-!
The arithmetic of the shifted-scale example. Graph existence is a separate
obligation; transcendence uses the explicitly accepted Gelfond--Schneider
interface shared with Section 4.
-/

namespace Universality.Section5

private theorem natural_algebraic (n : ℕ) : IsAlgebraic ℚ (n : ℝ) := by
  simpa using (isAlgebraic_algebraMap (A := ℝ) (n : ℚ))

theorem coprime_not_commensurate {a b : ℕ} (ha : 1 < a) (coprime : a.Coprime b) :
    ¬ ScaleCommensurate a b := by
  rintro ⟨m, n, hm, hn, equal⟩
  have coprimePowers : (a ^ m).Coprime (b ^ n) := (coprime.pow_left m).pow_right n
  rw [← equal, Nat.coprime_self] at coprimePowers
  have greater : 1 < a ^ m := one_lt_pow₀ ha (Nat.ne_of_gt hm)
  omega

theorem coprime_log_ratio_irrational {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (coprime : a.Coprime b) : Irrational (Real.log (a : ℝ) / Real.log (b : ℝ)) := by
  rintro ⟨rational, equality⟩
  exact coprime_not_commensurate ha coprime
    (rational_log_ratio_commensurate ha hb ⟨rational, equality.symm⟩)

theorem shifted_scale_coprime : Nat.Coprime 19 (19 ^ 100 + 480) := by
  decide

theorem shifted_scale_gt_one : 1 < 19 ^ 100 + 480 := by omega

theorem shifted_log_ratio_irrational :
    Irrational (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  exact coprime_log_ratio_irrational (by norm_num) shifted_scale_gt_one shifted_scale_coprime

theorem shifted_log_ratio_transcendental :
    Transcendental ℚ (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  apply Section4.logarithmic_dimension_transcendental
  · exact_mod_cast shifted_scale_gt_one
  · norm_num
  · exact natural_algebraic (19 ^ 100 + 480)
  · simpa using (isAlgebraic_algebraMap (A := ℝ) (19 : ℚ))
  · exact shifted_log_ratio_irrational

theorem shifted_dimension_transcendental (power : ℕ) (positive : 0 < power) :
    Transcendental ℚ
      (Real.log ((19 : ℝ) ^ power) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  have irrational : Irrational
      (Real.log ((19 : ℕ) ^ power : ℕ) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) :=
    coprime_log_ratio_irrational (one_lt_pow₀ (by norm_num) (Nat.ne_of_gt positive))
      shifted_scale_gt_one (shifted_scale_coprime.pow_left power)
  apply Section4.logarithmic_dimension_transcendental
  · exact_mod_cast shifted_scale_gt_one
  · positivity
  · exact natural_algebraic (19 ^ 100 + 480)
  · simpa using (isAlgebraic_algebraMap (A := ℝ) ((19 : ℚ) ^ power))
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using irrational

theorem shifted_three_dimensions_transcendental :
    Transcendental ℚ (Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) ∧
    Transcendental ℚ (Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) ∧
    Transcendental ℚ (Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) :=
  ⟨shifted_dimension_transcendental 232 (by norm_num),
    shifted_dimension_transcendental 219 (by norm_num),
    shifted_dimension_transcendental 70 (by norm_num)⟩

theorem shifted_dimensions_proportional :
    Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ) =
      (219 / 232 : ℚ) *
        (Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) ∧
    Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ) =
      (35 / 116 : ℚ) *
        (Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  simp only [Real.log_pow]
  push_cast
  constructor <;> ring

end Universality.Section5
