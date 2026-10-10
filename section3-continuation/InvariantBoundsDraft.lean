import IGSIII34.Probability.MixedMoments
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open scoped NNReal ENNReal

theorem exists_invariant_powerMoment_bound (edges : ℕ) (coefficient : ℝ≥0)
    (coefficientPositive : 0 < coefficient) {power : ℕ} (powerAtLeastTwo : 2 ≤ power)
    (coefficientPowerLarge : (edges : ℝ≥0) < coefficient ^ power) :
    ∃ bound : ℝ≥0, 1 ≤ bound ∧
      ((coefficient : ℝ≥0∞) ^ power)⁻¹ *
        ((edges : ℝ≥0∞) * bound + (edges : ℝ≥0∞) ^ power *
          (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) ≤ bound := by
  let base : ℝ≥0 := 1 + (edges : ℝ≥0) ^ power / (coefficient ^ power - edges)
  have baseAtLeastOne : 1 ≤ base := le_add_of_nonneg_right zero_le
  have denominatorPositive : 0 < coefficient ^ power - (edges : ℝ≥0) :=
    tsub_pos_iff_lt.mpr coefficientPowerLarge
  have baseInequality : (edges : ℝ≥0) * base + (edges : ℝ≥0) ^ power ≤ coefficient ^ power * base := by
    have quotientBound : (edges : ℝ≥0) ^ power ≤ (coefficient ^ power - edges) * base := by
      rw [mul_comm]
      apply (div_le_iff₀ denominatorPositive).mp
      exact le_add_of_nonneg_left zero_le
    have differenceIdentity : coefficient ^ power - (edges : ℝ≥0) + edges = coefficient ^ power :=
      tsub_add_cancel_of_le coefficientPowerLarge.le
    calc
      _ ≤ (edges : ℝ≥0) * base + (coefficient ^ power - edges) * base := add_le_add le_rfl quotientBound
      _ = ((coefficient ^ power - edges) + edges) * base := by ring
      _ = _ := by rw [differenceIdentity]
  refine ⟨base ^ (power - 1), one_le_pow₀ baseAtLeastOne, ?_⟩
  have powerPositive : 1 ≤ power := by omega
  have previousPositive : 1 ≤ power - 1 := by omega
  have exponentNonnegative : 0 ≤ ((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    have : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have exponentIdentity : (((power - 1 : ℕ) : ℝ) *
      (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) = ((power - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub powerPositive, Nat.cast_one]
    have denominatorNonzero : (power : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
      linarith
    field_simp
  have mixedPowerIdentity : (base ^ (power - 1)) ^
      (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) = base ^ (power - 2) := by
    rw [← NNReal.rpow_natCast base (power - 1), ← NNReal.rpow_mul,
      exponentIdentity, NNReal.rpow_natCast]
  have previousPowerIdentity : base ^ (power - 1) = base * base ^ (power - 2) := by
    have orderIdentity : power - 1 = (power - 2) + 1 := by omega
    rw [orderIdentity, pow_succ, mul_comm]
  have scalarBound : (coefficient ^ power)⁻¹ *
      ((edges : ℝ≥0) * base ^ (power - 1) + (edges : ℝ≥0) ^ power * base ^ (power - 2)) ≤
        base ^ (power - 1) := by
    apply (inv_mul_le_iff₀ (pow_pos coefficientPositive power)).mpr
    rw [previousPowerIdentity]
    calc
      _ = ((edges : ℝ≥0) * base + (edges : ℝ≥0) ^ power) * base ^ (power - 2) := by ring
      _ ≤ (coefficient ^ power * base) * base ^ (power - 2) := mul_le_mul_of_nonneg_right baseInequality zero_le
      _ = _ := by ring
  rw [← ENNReal.coe_rpow_of_nonneg _ exponentNonnegative, mixedPowerIdentity]
  convert ENNReal.coe_le_coe.mpr scalarBound using 1 <;>
    simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_pow,
      ENNReal.coe_natCast, ENNReal.coe_inv (pow_ne_zero power coefficientPositive.ne')]

theorem exists_all_invariant_powerMoment_bounds (edges : ℕ) (coefficient : ℝ≥0)
    (coefficientAboveOne : 1 < coefficient) :
    ∃ lowerOrder : ℕ, 2 ≤ lowerOrder ∧ ∃ bounds : ℕ → ℝ≥0, ∀ power, lowerOrder ≤ power →
      1 ≤ bounds power ∧
        ((coefficient : ℝ≥0∞) ^ power)⁻¹ *
          ((edges : ℝ≥0∞) * bounds power + (edges : ℝ≥0∞) ^ power *
            (bounds power : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) ≤ bounds power := by
  classical
  have eventuallyLarge : ∀ᶠ power : ℕ in Filter.atTop, (edges : ℝ≥0) < coefficient ^ power :=
    (tendsto_pow_atTop_atTop_of_one_lt coefficientAboveOne).eventually (Filter.eventually_gt_atTop _)
  obtain ⟨threshold, largeAbove⟩ := Filter.eventually_atTop.mp eventuallyLarge
  let lowerOrder := max 2 threshold
  have boundExists (power : ℕ) : ∃ bound : ℝ≥0, lowerOrder ≤ power →
      1 ≤ bound ∧ ((coefficient : ℝ≥0∞) ^ power)⁻¹ *
        ((edges : ℝ≥0∞) * bound + (edges : ℝ≥0∞) ^ power *
          (bound : ℝ≥0∞) ^ (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1))) ≤ bound := by
    by_cases highOrder : lowerOrder ≤ power
    · obtain ⟨bound, boundProperties⟩ := exists_invariant_powerMoment_bound edges coefficient
        (zero_lt_one.trans coefficientAboveOne) ((le_max_left 2 threshold).trans highOrder)
        (largeAbove power ((le_max_right 2 threshold).trans highOrder))
      exact ⟨bound, fun _ => boundProperties⟩
    · exact ⟨1, fun contradiction => (highOrder contradiction).elim⟩
  choose bounds boundProperties using boundExists
  exact ⟨lowerOrder, le_max_left _ _, bounds, boundProperties⟩

end
end IGSIII34.Probability
