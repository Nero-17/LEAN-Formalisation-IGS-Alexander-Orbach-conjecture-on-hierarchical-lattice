import IGSIII4.SpectralDensity.LogGrowth
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Bounded logarithmic errors from multiplicative bounds, with the full
polynomial correction retained. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology
open Asymptotics

theorem logarithm_polynomial_exponential
    (coefficient base : ℝ) (order depth : ℕ)
    (coefficientPositive : 0 < coefficient) (basePositive : 0 < base)
    (depthPositive : 0 < depth) :
    Real.log (coefficient * (depth : ℝ) ^ order * base ^ depth) =
      Real.log coefficient + (order : ℝ) * Real.log (depth : ℝ) +
        (depth : ℝ) * Real.log base := by
  have depthRealPositive : 0 < (depth : ℝ) := Nat.cast_pos.mpr depthPositive
  rw [Real.log_mul (mul_ne_zero (ne_of_gt coefficientPositive)
    (pow_ne_zero _ (ne_of_gt depthRealPositive))) (pow_ne_zero _ (ne_of_gt basePositive))]
  rw [Real.log_mul (ne_of_gt coefficientPositive) (pow_ne_zero _ (ne_of_gt depthRealPositive))]
  simp only [Real.log_pow]

theorem logarithmic_remainder_bounds_of_polynomial_exponential_bounds
    (growth : ℕ → ℝ) (lowerCoefficient upperCoefficient base : ℝ) (order : ℕ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (basePositive : 0 < base)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      lowerCoefficient * (depth : ℝ) ^ order * base ^ depth ≤ growth depth ∧
      growth depth ≤ upperCoefficient * (depth : ℝ) ^ order * base ^ depth) :
    ∀ᶠ depth : ℕ in atTop,
      Real.log lowerCoefficient ≤
        Real.log (growth depth) -
          ((depth : ℝ) * Real.log base + (order : ℝ) * Real.log (depth : ℝ)) ∧
      Real.log (growth depth) -
          ((depth : ℝ) * Real.log base + (order : ℝ) * Real.log (depth : ℝ)) ≤
        Real.log upperCoefficient := by
  filter_upwards [bounds, eventually_ge_atTop (1 : ℕ)] with depth depthBounds depthLarge
  have depthPositive : 0 < depth := by omega
  have depthRealPositive : 0 < (depth : ℝ) := Nat.cast_pos.mpr depthPositive
  have lowerTermPositive : 0 < lowerCoefficient * (depth : ℝ) ^ order * base ^ depth := by
    positivity
  have lower := Real.log_le_log lowerTermPositive depthBounds.1
  have upper := Real.log_le_log (lowerTermPositive.trans_le depthBounds.1) depthBounds.2
  rw [logarithm_polynomial_exponential lowerCoefficient base order depth
    lowerPositive basePositive depthPositive] at lower
  rw [logarithm_polynomial_exponential upperCoefficient base order depth
    upperPositive basePositive depthPositive] at upper
  constructor <;> linarith

theorem isBigO_one_of_eventually_bounded
    (remainder : ℕ → ℝ) (lower upper : ℝ)
    (bounds : ∀ᶠ depth : ℕ in atTop, lower ≤ remainder depth ∧ remainder depth ≤ upper) :
    remainder =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨max |lower| |upper|, ?_⟩
  filter_upwards [bounds] with depth depthBounds
  simp only [Real.norm_eq_abs, abs_one, mul_one]
  apply abs_le.mpr
  constructor
  · have := le_max_left |lower| |upper|
    have := neg_abs_le lower
    linarith [depthBounds.1]
  · exact depthBounds.2.trans ((le_abs_self upper).trans (le_max_right _ _))

theorem logarithmic_remainder_isBigO_of_polynomial_exponential_bounds
    (growth : ℕ → ℝ) (lowerCoefficient upperCoefficient base : ℝ) (order : ℕ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (basePositive : 0 < base)
    (bounds : ∀ᶠ depth : ℕ in atTop,
      lowerCoefficient * (depth : ℝ) ^ order * base ^ depth ≤ growth depth ∧
      growth depth ≤ upperCoefficient * (depth : ℝ) ^ order * base ^ depth) :
    (fun depth : ℕ => Real.log (growth depth) -
      ((depth : ℝ) * Real.log base + (order : ℝ) * Real.log (depth : ℝ)))
        =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  isBigO_one_of_eventually_bounded _ (Real.log lowerCoefficient) (Real.log upperCoefficient)
    (logarithmic_remainder_bounds_of_polynomial_exponential_bounds growth
      lowerCoefficient upperCoefficient base order lowerPositive upperPositive basePositive bounds)

end
end IGSIII4.SpectralDensity
