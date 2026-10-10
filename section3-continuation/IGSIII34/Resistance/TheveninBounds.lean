import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
The one-edge numerical estimate used in Lemma electrical-comparison. This
proves the rational bounds for the Thevenin current formula; deriving that
formula from the finite network and integrating over independent edge pairs
remain separate obligations.
-/

set_option autoImplicit false

namespace IGSIII34.Resistance

noncomputable section

theorem thevenin_ratio_bounds {resistance background : ℝ}
    (resistancePositive : 0 < resistance) (backgroundNonnegative : 0 ≤ background) :
    min 1 resistance⁻¹ ≤ (1 + background) / (resistance + background) ∧
      (1 + background) / (resistance + background) ≤ max 1 resistance⁻¹ := by
  have denominatorPositive : 0 < resistance + background := by linarith
  by_cases smallResistance : resistance ≤ 1
  · have inverseLarge : 1 ≤ resistance⁻¹ := (one_le_inv₀ resistancePositive).mpr smallResistance
    rw [min_eq_left inverseLarge, max_eq_right inverseLarge]
    constructor
    · rw [le_div_iff₀ denominatorPositive]
      linarith
    · rw [div_le_iff₀ denominatorPositive]
      apply (mul_le_mul_iff_of_pos_right resistancePositive).mp
      have reciprocal : resistance⁻¹ * resistance = 1 := inv_mul_cancel₀ (ne_of_gt resistancePositive)
      calc
        (1 + background) * resistance = resistance + background * resistance := by ring
        _ ≤ resistance + background := by nlinarith
        _ = (resistance⁻¹ * (resistance + background)) * resistance := by
          field_simp
  · have largeResistance : 1 ≤ resistance := le_of_lt (lt_of_not_ge smallResistance)
    have inverseSmall : resistance⁻¹ ≤ 1 := (inv_le_one₀ resistancePositive).mpr largeResistance
    rw [min_eq_right inverseSmall, max_eq_left inverseSmall]
    constructor
    · rw [le_div_iff₀ denominatorPositive]
      apply (mul_le_mul_iff_of_pos_right resistancePositive).mp
      calc
        (resistance⁻¹ * (resistance + background)) * resistance = resistance + background := by
          field_simp
        _ ≤ (1 + background) * resistance := by nlinarith
    · rw [div_le_iff₀ denominatorPositive]
      linarith

theorem thevenin_current_sq_bounds {resistance background amplitude : ℝ}
    (resistancePositive : 0 < resistance) (backgroundNonnegative : 0 ≤ background) :
    min 1 (resistance⁻¹ ^ 2) * (amplitude / (1 + background)) ^ 2 ≤
      (amplitude / (resistance + background)) ^ 2 ∧
    (amplitude / (resistance + background)) ^ 2 ≤
      max 1 (resistance⁻¹ ^ 2) * (amplitude / (1 + background)) ^ 2 := by
  have ratioBounds := thevenin_ratio_bounds resistancePositive backgroundNonnegative
  have backgroundPositive : 0 < 1 + background := by linarith
  have denominatorPositive : 0 < resistance + background := by linarith
  have factorization : amplitude / (resistance + background) =
      ((1 + background) / (resistance + background)) * (amplitude / (1 + background)) := by
    field_simp
  rw [factorization, mul_pow]
  have lowerSquare : min 1 (resistance⁻¹ ^ 2) ≤
      ((1 + background) / (resistance + background)) ^ 2 := by
    by_cases small : resistance⁻¹ ≤ 1
    · rw [min_eq_right (by nlinarith [inv_nonneg.mpr resistancePositive.le])]
      have lower : resistance⁻¹ ≤ (1 + background) / (resistance + background) := by
        simpa [min_eq_right small] using ratioBounds.1
      nlinarith [inv_nonneg.mpr resistancePositive.le]
    · have large : 1 ≤ resistance⁻¹ := le_of_lt (lt_of_not_ge small)
      rw [min_eq_left (by nlinarith)]
      have lower : 1 ≤ (1 + background) / (resistance + background) := by
        simpa [min_eq_left large] using ratioBounds.1
      nlinarith
  have upperSquare : ((1 + background) / (resistance + background)) ^ 2 ≤
      max 1 (resistance⁻¹ ^ 2) := by
    have ratioNonnegative := (div_pos backgroundPositive denominatorPositive).le
    by_cases small : resistance⁻¹ ≤ 1
    · rw [max_eq_left (by nlinarith [inv_nonneg.mpr resistancePositive.le])]
      have upper : (1 + background) / (resistance + background) ≤ 1 := by
        simpa [max_eq_left small] using ratioBounds.2
      nlinarith
    · have large : 1 ≤ resistance⁻¹ := le_of_lt (lt_of_not_ge small)
      rw [max_eq_right (by nlinarith)]
      have upper : (1 + background) / (resistance + background) ≤ resistance⁻¹ := by
        simpa [max_eq_right large] using ratioBounds.2
      nlinarith
  exact ⟨mul_le_mul_of_nonneg_right lowerSquare (sq_nonneg _),
    mul_le_mul_of_nonneg_right upperSquare (sq_nonneg _)⟩

end
end IGSIII34.Resistance
