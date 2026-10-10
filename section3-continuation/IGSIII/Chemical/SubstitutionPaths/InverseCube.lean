import Mathlib.Analysis.MeanInequalitiesPow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open scoped BigOperators

theorem inverse_cube_weighted_mean {Index : Type*} [Fintype Index]
    (weight value : Index → ℝ) (weightNonnegative : ∀ index, 0 ≤ weight index)
    (weightNormalized : ∑ index, weight index = 1) (valuePositive : ∀ index, 0 < value index) :
    (∑ index, weight index * value index)⁻¹ ^ 3 ≤
      ∑ index, weight index * (value index)⁻¹ ^ 3 := by
  have comparison := Real.zpow_arith_mean_le_arith_mean_zpow Finset.univ weight value
    (fun index _ => weightNonnegative index) weightNormalized
    (fun index _ => valuePositive index) (-3)
  simpa only [zpow_neg, zpow_ofNat, inv_pow] using comparison

theorem inverse_cube_sum {Index : Type*} [DecidableEq Index]
    (path : Finset Index) (nonempty : path.Nonempty)
    (value : Index → ℝ) (positive : ∀ index ∈ path, 0 < value index) :
    (∑ index ∈ path, value index)⁻¹ ^ 3 ≤
      ((path.card : ℝ)⁻¹) ^ 4 * ∑ index ∈ path, (value index)⁻¹ ^ 3 := by
  have cardinalityPositive : 0 < (path.card : ℝ) := by exact_mod_cast nonempty.card_pos
  have comparison := Real.zpow_arith_mean_le_arith_mean_zpow path
    (fun _ => (path.card : ℝ)⁻¹) value
    (fun _ _ => inv_nonneg.mpr cardinalityPositive.le)
    (by simpa only [Finset.sum_const, nsmul_eq_mul] using mul_inv_cancel₀ cardinalityPositive.ne')
    positive (-3)
  simp only [zpow_neg, zpow_ofNat, ← inv_pow, ← Finset.mul_sum] at comparison
  have scaled := mul_le_mul_of_nonneg_left comparison
    (pow_nonneg (inv_nonneg.mpr cardinalityPositive.le) 3)
  have leftIdentity : ((path.card : ℝ)⁻¹) ^ 3 *
      (((path.card : ℝ)⁻¹ * ∑ index ∈ path, value index)⁻¹ ^ 3) =
        (∑ index ∈ path, value index)⁻¹ ^ 3 := by
    calc
      _ = (((path.card : ℝ)⁻¹ * path.card) *
          (∑ index ∈ path, value index)⁻¹) ^ 3 := by rw [mul_inv_rev, inv_inv]; ring
      _ = _ := by rw [inv_mul_cancel₀ cardinalityPositive.ne', one_mul]
  rw [leftIdentity] at scaled
  calc
    _ ≤ ((path.card : ℝ)⁻¹) ^ 3 *
        ((path.card : ℝ)⁻¹ * ∑ index ∈ path, (value index)⁻¹ ^ 3) := scaled
    _ = _ := by ring

end IGSIII.Chemical.Substitution
