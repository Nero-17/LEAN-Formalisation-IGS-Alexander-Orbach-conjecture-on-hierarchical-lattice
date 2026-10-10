import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Point evaluation and the component resolvent bound

These analytic lemmas prove the averaging step of Appendix B. Their resistance
inequality is an explicit input; construction of the actual limiting resistance
form is a separate obligation, not a field silently assumed here.
-/

set_option autoImplicit false

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory

theorem square_le_twice_square_add_twice_square (first second : ℝ) :
    first ^ 2 ≤ 2 * second ^ 2 + 2 * (first - second) ^ 2 := by
  nlinarith [sq_nonneg (first - 2 * second)]

theorem point_evaluation_le_of_resistance_inequality
    {Space : Type*} [MeasurableSpace Space]
    (measure : Measure Space) [IsFiniteMeasure measure]
    (function : Space → ℝ) (point : Space) (diameter energy : ℝ)
    (massPositive : 0 < measure.real Set.univ)
    (squareIntegrable : Integrable (fun other => function other ^ 2) measure)
    (resistanceBound : ∀ᵐ other ∂measure,
      (function point - function other) ^ 2 ≤ diameter * energy) :
    function point ^ 2 ≤
      2 / measure.real Set.univ * (∫ other, function other ^ 2 ∂measure) +
        2 * diameter * energy := by
  have pointwise : ∀ᵐ other ∂measure,
      function point ^ 2 ≤ 2 * function other ^ 2 + 2 * diameter * energy := by
    filter_upwards [resistanceBound] with other bound
    have squareBound := square_le_twice_square_add_twice_square
      (function point) (function other)
    linarith
  have averaged := integral_mono_ae (integrable_const (function point ^ 2))
    ((squareIntegrable.const_mul 2).add (integrable_const (2 * diameter * energy))) pointwise
  change (∫ _other, function point ^ 2 ∂measure) ≤
    ∫ other, 2 * function other ^ 2 + 2 * diameter * energy ∂measure at averaged
  rw [integral_add (squareIntegrable.const_mul 2)
    (integrable_const (2 * diameter * energy)), integral_const_mul,
    integral_const, integral_const, smul_eq_mul, smul_eq_mul] at averaged
  have divided : function point ^ 2 ≤
      (2 * (∫ other, function other ^ 2 ∂measure) +
        measure.real Set.univ * (2 * diameter * energy)) / measure.real Set.univ :=
    (le_div_iff₀ massPositive).mpr (by simpa [mul_comm] using averaged)
  calc
    _ ≤ _ := divided
    _ = _ := by field_simp [massPositive.ne']

theorem evaluation_quotient_le_component_bound
    (value energy squareIntegral mass parameter diameter : ℝ)
    (energyNonnegative : 0 ≤ energy) (squareIntegralNonnegative : 0 ≤ squareIntegral)
    (massPositive : 0 < mass) (parameterPositive : 0 < parameter)
    (diameterNonnegative : 0 ≤ diameter)
    (evaluationBound : value ^ 2 ≤ 2 / mass * squareIntegral + 2 * diameter * energy) :
    value ^ 2 / (energy + parameter * squareIntegral) ≤
      2 * max (1 / (parameter * mass)) diameter := by
  have maximumNonnegative : 0 ≤ max (1 / (parameter * mass)) diameter :=
    diameterNonnegative.trans (le_max_right _ _)
  by_cases denominatorZero : energy + parameter * squareIntegral = 0
  · simp only [denominatorZero, div_zero]
    positivity
  have denominatorPositive : 0 < energy + parameter * squareIntegral :=
    lt_of_le_of_ne (add_nonneg energyNonnegative
      (mul_nonneg parameterPositive.le squareIntegralNonnegative)) (Ne.symm denominatorZero)
  apply (div_le_iff₀ denominatorPositive).mpr
  have firstBound : 2 / mass * squareIntegral ≤
      2 * max (1 / (parameter * mass)) diameter * (parameter * squareIntegral) := by
    have comparison := mul_le_mul_of_nonneg_right
      (le_max_left (1 / (parameter * mass)) diameter)
      (mul_nonneg parameterPositive.le squareIntegralNonnegative)
    have cancellation : 1 / (parameter * mass) * (parameter * squareIntegral) =
        squareIntegral / mass := by field_simp
    rw [cancellation] at comparison
    calc
      _ = 2 * (squareIntegral / mass) := by ring
      _ ≤ 2 * (max (1 / (parameter * mass)) diameter *
          (parameter * squareIntegral)) :=
        mul_le_mul_of_nonneg_left comparison (by norm_num)
      _ = _ := by ring
  have secondBound : 2 * diameter * energy ≤
      2 * max (1 / (parameter * mass)) diameter * energy := by
    nlinarith [mul_le_mul_of_nonneg_right
      (le_max_right (1 / (parameter * mass)) diameter) energyNonnegative]
  nlinarith

theorem component_resolvent_quotient_bound
    {Space : Type*} [MeasurableSpace Space]
    (measure : Measure Space) [IsFiniteMeasure measure]
    (function : Space → ℝ) (point : Space) (diameter energy parameter : ℝ)
    (massPositive : 0 < measure.real Set.univ)
    (squareIntegrable : Integrable (fun other => function other ^ 2) measure)
    (energyNonnegative : 0 ≤ energy) (parameterPositive : 0 < parameter)
    (diameterNonnegative : 0 ≤ diameter)
    (resistanceBound : ∀ᵐ other ∂measure,
      (function point - function other) ^ 2 ≤ diameter * energy) :
    function point ^ 2 / (energy + parameter * (∫ other, function other ^ 2 ∂measure)) ≤
      2 * max (1 / (parameter * measure.real Set.univ)) diameter := by
  exact evaluation_quotient_le_component_bound _ _ _ _ _ _ energyNonnegative
    (integral_nonneg (fun other => sq_nonneg (function other))) massPositive
    parameterPositive diameterNonnegative
    (point_evaluation_le_of_resistance_inequality measure function point diameter energy
      massPositive squareIntegrable resistanceBound)

end
end IGSIII34.Spectral

