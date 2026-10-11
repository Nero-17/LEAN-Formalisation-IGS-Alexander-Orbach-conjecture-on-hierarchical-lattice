import Universality.Probability.FourierL1Dominated

namespace Universality
noncomputable section
open MeasureTheory

theorem characteristic_weighted_integrable (characteristic : ℝ → ℂ)
    (hmeasurable : AEStronglyMeasurable characteristic)
    (hnorm : ∀ t, ‖characteristic t‖ ≤ 1)
    (order : ℕ) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hpolynomial : ∀ t, 1 ≤ |t| → ‖characteristic t‖ * |t| ^ (order + 2) ≤ constant) :
    Integrable (fun t : ℝ => ‖t‖ ^ order * ‖characteristic t‖) := by
  have henvelope : Integrable (fun t : ℝ => (2 * constant + 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply henvelope.mono'
  · exact ((continuous_norm.pow order).aestronglyMeasurable.mul hmeasurable.norm)
  · apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + t ^ 2), Real.norm_eq_abs]
    have hvalue0 : 0 ≤ |t| ^ order * ‖characteristic t‖ :=
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)
    by_cases ht : 1 ≤ |t|
    · have hquadratic : (|t| ^ order * ‖characteristic t‖) * t ^ 2 ≤ constant := by
        have := hpolynomial t ht
        rw [pow_add, sq_abs] at this
        nlinarith
      have hsquare : 1 ≤ t ^ 2 := by
        simpa only [one_pow, sq_abs] using
          (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg t)).mpr ht
      have hvalue : |t| ^ order * ‖characteristic t‖ ≤ constant := by
        nlinarith
      nlinarith
    · have ht' : |t| ≤ 1 := (lt_of_not_ge ht).le
      have hvalue : |t| ^ order * ‖characteristic t‖ ≤ 1 := by
        exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) ht') (hnorm t)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
      have hsquare : t ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).mpr ht'
      nlinarith

end
end Universality
