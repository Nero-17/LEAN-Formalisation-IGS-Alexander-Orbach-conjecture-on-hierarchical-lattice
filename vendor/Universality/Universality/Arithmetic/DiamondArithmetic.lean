import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Universality.Arithmetic.NoIntegerPower
import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Examples.DiamondClassical

/-!
# Exact quadratic-field arithmetic for the diamond example

The nonsquare certificate is proved over the actual intermediate field
`Q(sqrt 5)`, with membership reduced to rational coordinates by field closure.
No transcendence theorem is needed for this certificate.
-/

namespace Universality.Section4
noncomputable section
open Polynomial

theorem sqrt_five_rational_relation (a b : ℚ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 5 = 0) : a = 0 ∧ b = 0 := by
  have hirrational : Irrational (Real.sqrt (5 : ℝ)) := by norm_num
  by_cases hb : b = 0
  · constructor
    · exact_mod_cast (by simpa [hb] using h : (a : ℝ) = 0)
    · exact hb
  · have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hsqrt : ((-a / b : ℚ) : ℝ) = Real.sqrt 5 := by
      push_cast
      apply (div_eq_iff hbReal).mpr
      linarith
    exact False.elim (hirrational ⟨-a / b, hsqrt⟩)

theorem sqrt_five_adjoin_coordinates {value : ℝ}
    (hvalue : value ∈ IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}) :
    ∃ a b : ℚ, value = (a : ℝ) + (b : ℝ) * Real.sqrt 5 := by
  induction hvalue using IntermediateField.adjoin_induction with
  | mem value hvalue =>
      simp only [Set.mem_singleton_iff] at hvalue
      subst value
      exact ⟨0, 1, by norm_num⟩
  | algebraMap value => exact ⟨value, 0, by simp⟩
  | add value other hvalue hother ihvalue ihother =>
      obtain ⟨a, b, rfl⟩ := ihvalue
      obtain ⟨c, d, rfl⟩ := ihother
      exact ⟨a + c, b + d, by push_cast; ring⟩
  | inv value hvalue ihvalue =>
      obtain ⟨a, b, rfl⟩ := ihvalue
      by_cases hzero : (a : ℝ) + (b : ℝ) * Real.sqrt 5 = 0
      · exact ⟨0, 0, by simp [hzero]⟩
      · have hconjugate : (a : ℝ) - (b : ℝ) * Real.sqrt 5 ≠ 0 := by
          intro h
          have hrelation : (a : ℝ) + ((-b : ℚ) : ℝ) * Real.sqrt 5 = 0 := by
            push_cast
            linarith
          obtain ⟨ha, hb⟩ := sqrt_five_rational_relation a (-b) hrelation
          simp only [neg_eq_zero] at hb
          simp [ha, hb] at hzero
        have hnorm : (a : ℝ) ^ 2 - 5 * (b : ℝ) ^ 2 ≠ 0 := by
          have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
          have hproduct : ((a : ℝ) + (b : ℝ) * Real.sqrt 5) *
              ((a : ℝ) - (b : ℝ) * Real.sqrt 5) =
              (a : ℝ) ^ 2 - 5 * (b : ℝ) ^ 2 := by nlinarith
          rw [← hproduct]
          exact mul_ne_zero hzero hconjugate
        refine ⟨a / (a ^ 2 - 5 * b ^ 2), -b / (a ^ 2 - 5 * b ^ 2), ?_⟩
        push_cast
        apply inv_eq_of_mul_eq_one_right
        have hnorm' : (a : ℝ) ^ 2 - (b : ℝ) ^ 2 * 5 ≠ 0 := by
          intro hzero'
          apply hnorm
          nlinarith
        field_simp [hnorm, hnorm']
        linear_combination -(b : ℝ) ^ 2 *
          (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))
  | mul value other hvalue hother ihvalue ihother =>
      obtain ⟨a, b, rfl⟩ := ihvalue
      obtain ⟨c, d, rfl⟩ := ihother
      refine ⟨a * c + 5 * b * d, a * d + b * c, ?_⟩
      push_cast
      linear_combination (b : ℝ) * (d : ℝ) *
        (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))

theorem diamond_discriminant_not_square_coordinates (a b : ℚ) :
    ((a : ℝ) + (b : ℝ) * Real.sqrt 5) ^ 2 ≠ 73 - 32 * Real.sqrt 5 := by
  intro hsquare
  have hrelation : ((a ^ 2 + 5 * b ^ 2 - 73 : ℚ) : ℝ) +
      ((2 * a * b + 32 : ℚ) : ℝ) * Real.sqrt 5 = 0 := by
    push_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  obtain ⟨hconstant, hlinear⟩ :=
    sqrt_five_rational_relation (a ^ 2 + 5 * b ^ 2 - 73) (2 * a * b + 32) hrelation
  have hnorm : (a ^ 2 - 5 * b ^ 2) ^ 2 = (209 : ℚ) := by
    nlinarith [sq_nonneg (a ^ 2 + 5 * b ^ 2 - 73),
      sq_nonneg (2 * a * b + 32)]
  have hnotSquare : ¬ IsSquare (209 : ℚ) := by norm_num
  apply hnotSquare
  exact ⟨a ^ 2 - 5 * b ^ 2, by nlinarith [hnorm]⟩

/-- The discriminant `73 - 32 sqrt 5` has no square root in the critical
quadratic field; its rational norm is the nonsquare integer 209. -/
theorem diamond_discriminant_not_square_in_field {value : ℝ}
    (hvalue : value ∈ IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}) :
    value ^ 2 ≠ 73 - 32 * Real.sqrt 5 := by
  obtain ⟨a, b, rfl⟩ := sqrt_five_adjoin_coordinates hvalue
  exact diamond_discriminant_not_square_coordinates a b

theorem diamond_discriminant_pos : 0 < 73 - 32 * Real.sqrt (5 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]

theorem diamond_discriminant_sqrt_not_mem :
    Real.sqrt (73 - 32 * Real.sqrt (5 : ℝ)) ∉
      IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)} := by
  intro hmember
  exact diamond_discriminant_not_square_in_field hmember
    (Real.sq_sqrt diamond_discriminant_pos.le)

theorem diamond_critical_field_expression :
    IntermediateField.adjoin ℚ {(Real.sqrt (5 : ℝ) - 1) / 2} =
      IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact (IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}).div_mem
      ((IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}).sub_mem
        (IntermediateField.mem_adjoin_simple_self ℚ _) (one_mem _))
      (natCast_mem _ 2)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hequal : Real.sqrt (5 : ℝ) = 2 * ((Real.sqrt 5 - 1) / 2) + 1 := by ring
    have hmember := (IntermediateField.adjoin ℚ {(Real.sqrt (5 : ℝ) - 1) / 2}).add_mem
      ((IntermediateField.adjoin ℚ {(Real.sqrt (5 : ℝ) - 1) / 2}).mul_mem
        (natCast_mem _ 2) (IntermediateField.mem_adjoin_simple_self ℚ _)) (one_mem _)
    norm_num only [Nat.cast_ofNat] at hmember
    rwa [← hequal] at hmember

theorem diamond_mass_expression_not_mem :
    7 - 2 * Real.sqrt (5 : ℝ) + Real.sqrt (73 - 32 * Real.sqrt (5 : ℝ)) ∉
      IntermediateField.adjoin ℚ {(Real.sqrt (5 : ℝ) - 1) / 2} := by
  rw [diamond_critical_field_expression]
  intro hmember
  have hbase : 7 - 2 * Real.sqrt (5 : ℝ) ∈
      IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)} :=
    (IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}).sub_mem (natCast_mem _ 7)
      ((IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}).mul_mem
        (natCast_mem _ 2) (IntermediateField.mem_adjoin_simple_self ℚ _))
  apply diamond_discriminant_sqrt_not_mem
  have hsubtract := (IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)}).sub_mem hmember hbase
  simpa only [add_sub_cancel_left] using hsubtract

theorem sqrt_five_power_coordinates (a b : ℚ) (exponent : ℕ) :
    ∃ c d : ℚ,
      ((a : ℝ) + (b : ℝ) * Real.sqrt 5) ^ exponent =
        (c : ℝ) + (d : ℝ) * Real.sqrt 5 ∧
      ((a : ℝ) - (b : ℝ) * Real.sqrt 5) ^ exponent =
        (c : ℝ) - (d : ℝ) * Real.sqrt 5 := by
  induction exponent with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ exponent ih =>
      obtain ⟨c, d, hplus, hminus⟩ := ih
      refine ⟨a * c + 5 * b * d, a * d + b * c, ?_, ?_⟩
      · rw [pow_succ, hplus]
        push_cast
        linear_combination (b : ℝ) * (d : ℝ) *
          (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))
      · rw [pow_succ, hminus]
        push_cast
        linear_combination (b : ℝ) * (d : ℝ) *
          (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))

theorem diamond_pivotal_expression_gt_one : 1 < 6 - 2 * Real.sqrt (5 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]

/-- Conjugating the two rational coordinates rules out every positive integer
power of the diamond multiplier without using the general Hensel argument. -/
theorem diamond_pivotal_expression_no_integer_power (exponent : ℕ) (hexponent : 0 < exponent)
    (integer : ℤ) : (6 - 2 * Real.sqrt (5 : ℝ)) ^ exponent ≠ integer := by
  intro hpower
  obtain ⟨a, b, hfirst, hsecond⟩ := sqrt_five_power_coordinates 6 (-2) exponent
  norm_num at hfirst hsecond
  simp only [← sub_eq_add_neg] at hfirst
  have hrelation : ((a - integer : ℚ) : ℝ) + (b : ℝ) * Real.sqrt 5 = 0 := by
    push_cast
    linarith
  obtain ⟨_, hb⟩ := sqrt_five_rational_relation (a - integer) b hrelation
  have hequal : (6 - 2 * Real.sqrt (5 : ℝ)) ^ exponent =
      (6 + 2 * Real.sqrt (5 : ℝ)) ^ exponent := by
    simp only [hb, Rat.cast_zero, zero_mul, add_zero, sub_zero] at hfirst hsecond
    exact hfirst.trans hsecond.symm
  have hlt : 6 - 2 * Real.sqrt (5 : ℝ) < 6 + 2 * Real.sqrt (5 : ℝ) := by
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)]
  exact (ne_of_lt (pow_lt_pow_left₀ hlt
    (le_of_lt (lt_trans zero_lt_one diamond_pivotal_expression_gt_one)) hexponent.ne')) hequal

theorem diamond_pivotal_expression_isAlgebraic :
    IsAlgebraic ℚ (6 - 2 * Real.sqrt (5 : ℝ)) := by
  refine ⟨(Polynomial.X ^ 2 - Polynomial.C 12 * Polynomial.X + Polynomial.C 16 : ℚ[X]), ?_, ?_⟩
  · intro hzero
    have hcoefficient := congrArg (fun polynomial : ℚ[X] => polynomial.coeff 2) hzero
    norm_num at hcoefficient
  · simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

theorem diamond_pivotal_dimension_transcendental :
    Transcendental ℚ (Real.log (6 - 2 * Real.sqrt (5 : ℝ)) / Real.log 2) := by
  exact logarithmic_dimension_transcendental_of_no_integer_power 2 _ (by norm_num)
    diamond_pivotal_expression_gt_one diamond_pivotal_expression_isAlgebraic
    diamond_pivotal_expression_no_integer_power

end
end Universality.Section4

namespace Universality
noncomputable section
open Matrix FiniteNetwork

theorem diamond_actual_critical_field :
    IntermediateField.adjoin ℚ {diamondCriticalProbability} =
      IntermediateField.adjoin ℚ {Real.sqrt (5 : ℝ)} :=
  Section4.diamond_critical_field_expression

theorem diamond_actual_mass_nonsplit :
    (spectralRadius ℂ ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {diamondCriticalProbability} := by
  have hpositive := positiveRoot_pos _ diamond_critical_block_positive
  rw [diamond_critical_positiveRoot] at hpositive
  rw [diamond_critical_spectralRadius, ENNReal.toReal_ofReal hpositive.le]
  exact Section4.diamond_mass_expression_not_mem

theorem diamond_actual_pivotal_no_integer_power (exponent : ℕ) (hexponent : 0 < exponent)
    (integer : ℤ) :
    deriv diamondNetwork.reliability diamondCriticalProbability ^ exponent ≠ integer := by
  rw [diamond_critical_response]
  exact Section4.diamond_pivotal_expression_no_integer_power exponent hexponent integer

theorem diamond_actual_pivotal_dimension_transcendental :
    Transcendental ℚ (diamondRule.criticalDimensions diamondCriticalProbability 2) := by
  change Transcendental ℚ
    (Real.log (deriv diamondNetwork.reliability diamondCriticalProbability) /
      Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target))
  rw [diamond_terminal_distance, diamond_critical_response]
  exact Section4.diamond_pivotal_dimension_transcendental

end
end Universality

#print axioms Universality.Section4.sqrt_five_adjoin_coordinates
#print axioms Universality.Section4.diamond_discriminant_not_square_in_field
#print axioms Universality.Section4.diamond_discriminant_sqrt_not_mem
#print axioms Universality.Section4.diamond_mass_expression_not_mem
#print axioms Universality.Section4.diamond_pivotal_expression_no_integer_power
#print axioms Universality.Section4.diamond_pivotal_dimension_transcendental
#print axioms Universality.diamond_actual_critical_field
#print axioms Universality.diamond_actual_mass_nonsplit
#print axioms Universality.diamond_actual_pivotal_no_integer_power
#print axioms Universality.diamond_actual_pivotal_dimension_transcendental
