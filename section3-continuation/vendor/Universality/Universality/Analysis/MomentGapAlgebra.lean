import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Universality
noncomputable section
open Filter

/-- A positive-part increment attains its full step exactly after its
starting point has reached the nonnegative half-line. -/
theorem positive_part_increment_eq_iff (position step : ℝ) (hstep : 0 < step) :
    max (position + step) 0 - max position 0 = step ↔ 0 ≤ position := by
  by_cases hposition : 0 ≤ position
  · rw [max_eq_left hposition, max_eq_left (by linarith : 0 ≤ position + step)]
    constructor
    · intro _
      exact hposition
    · intro _
      ring
  · have hn : position < 0 := lt_of_not_ge hposition
    rw [max_eq_right hn.le]
    by_cases hnext : 0 ≤ position + step
    · rw [max_eq_left hnext]
      constructor <;> intro hh <;> linarith
    · rw [max_eq_right (le_of_lt (lt_of_not_ge hnext))]
      constructor <;> intro hh <;> linarith

/-- The common-gap criterion at every positive integer moment order. -/
theorem all_positive_part_gaps_eq_iff (growth volume : ℝ) (hgrowth : 0 < growth) :
    (∀ order : ℕ, 1 ≤ order →
      max (((order + 2 : ℕ) : ℝ) * growth - volume) 0 -
        max (((order + 1 : ℕ) : ℝ) * growth - volume) 0 = growth) ↔
      volume ≤ 2 * growth := by
  constructor
  · intro hall
    have hh := hall 1 (by omega)
    norm_num at hh
    have heq : 3 * growth - volume = (2 * growth - volume) + growth := by ring
    rw [heq] at hh
    have := (positive_part_increment_eq_iff (2 * growth - volume) growth hgrowth).mp hh
    linarith
  · intro hvolume order horder
    have hcast : (1 : ℝ) ≤ order := by exact_mod_cast horder
    have hproduct := mul_le_mul_of_nonneg_right hcast hgrowth.le
    have hposition : 0 ≤ (((order + 1 : ℕ) : ℝ) * growth - volume) := by
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have heq : (((order + 2 : ℕ) : ℝ) * growth - volume) =
        (((order + 1 : ℕ) : ℝ) * growth - volume) + growth := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [heq]
    exact (positive_part_increment_eq_iff _ _ hgrowth).mpr hposition

/-- Every sufficiently high moment order lies in the common-gap regime. -/
theorem eventually_positive_part_gaps_eq (growth volume : ℝ) (hgrowth : 0 < growth) :
    ∀ᶠ order : ℕ in atTop,
      max (((order + 2 : ℕ) : ℝ) * growth - volume) 0 -
        max (((order + 1 : ℕ) : ℝ) * growth - volume) 0 = growth := by
  obtain ⟨start, hstart⟩ := exists_nat_gt (volume / growth)
  filter_upwards [eventually_ge_atTop start] with order horder
  have hcast : (start : ℝ) ≤ order := by exact_mod_cast horder
  have hvolume : volume < (start : ℝ) * growth := (div_lt_iff₀ hgrowth).mp hstart
  have hproduct := mul_le_mul_of_nonneg_right hcast hgrowth.le
  have hposition : 0 ≤ (((order + 1 : ℕ) : ℝ) * growth - volume) := by
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have heq : (((order + 2 : ℕ) : ℝ) * growth - volume) =
      (((order + 1 : ℕ) : ℝ) * growth - volume) + growth := by
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [heq]
  exact (positive_part_increment_eq_iff _ _ hgrowth).mpr hposition

end
end Universality
