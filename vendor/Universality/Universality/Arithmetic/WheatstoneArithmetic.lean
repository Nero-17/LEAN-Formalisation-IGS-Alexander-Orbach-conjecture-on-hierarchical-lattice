import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Universality.Arithmetic.DimensionRank
import Universality.Arithmetic.CommonPrimitiveBase
import Universality.Percolation.ReliabilityDerivative

/-!
# The exact arithmetic certificate for the Wheatstone example

The integer prime-valuation argument is proved directly. There is no external
transcendence theorem in this certificate. The actual graph response bridge is
separate, using its previously computed scale, volume and pivotal multiplier.
-/

namespace Universality.Section4

private theorem prime_valuation_product (prime : ℕ) [Fact prime.Prime]
    (a b c : ℤ) :
    padicValRat prime ((2 : ℚ) ^ a * 5 ^ b * 13 ^ c) =
      a * padicValRat prime 2 + b * padicValRat prime 5 + c * padicValRat prime 13 := by
  rw [padicValRat.mul (mul_ne_zero (zpow_ne_zero a (by norm_num))
      (zpow_ne_zero b (by norm_num))) (zpow_ne_zero c (by norm_num)),
    padicValRat.mul (zpow_ne_zero a (by norm_num)) (zpow_ne_zero b (by norm_num))]
  simp

theorem two_five_thirteen_zpow_independent (a b c : ℤ)
    (h : (2 : ℚ) ^ a * 5 ^ b * 13 ^ c = 1) : a = 0 ∧ b = 0 ∧ c = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h2 := congrArg (padicValRat 2) h
  have h5 := congrArg (padicValRat 5) h
  have h13 := congrArg (padicValRat 13) h
  rw [prime_valuation_product] at h2 h5 h13
  have h25 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h213 : padicValNat 2 13 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h52 : padicValNat 5 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h513 : padicValNat 5 13 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h132 : padicValNat 13 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h135 : padicValNat 13 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  norm_num [padicValRat, padicValInt, h25, h213, h52, h513, h132, h135] at h2 h5 h13
  exact ⟨h2, h5, h13⟩

theorem two_five_thirteen_integer_log_relation (a b c : ℤ)
    (h : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 5 +
      (c : ℝ) * Real.log 13 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hreal : (2 : ℝ) ^ a * 5 ^ b * 13 ^ c = 1 := by
    apply Real.log_injOn_pos
      (show 0 < (2 : ℝ) ^ a * 5 ^ b * 13 ^ c by positivity)
      (show 0 < (1 : ℝ) by norm_num)
    rw [Real.log_mul (mul_ne_zero (zpow_ne_zero a (by norm_num))
        (zpow_ne_zero b (by norm_num))) (zpow_ne_zero c (by norm_num)),
      Real.log_mul (zpow_ne_zero a (by norm_num)) (zpow_ne_zero b (by norm_num)),
      Real.log_zpow, Real.log_zpow, Real.log_zpow, Real.log_one]
    exact h
  apply two_five_thirteen_zpow_independent a b c
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_one] using hreal

theorem wheatstone_integer_dimension_relation (a b c : ℤ)
    (h : (a : ℝ) + (b : ℝ) * (Real.log 5 / Real.log 2) +
      (c : ℝ) * (Real.log (13 / 8) / Real.log 2) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hthermal : Real.log (13 / 8 : ℝ) = Real.log 13 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog8]
  rw [hthermal] at h
  have hscaled := congrArg (fun value : ℝ => value * Real.log 2) h
  simp only [add_mul, mul_assoc, div_mul_cancel₀ _ hlog2, zero_mul] at hscaled
  have hrelation : ((a - 3 * c : ℤ) : ℝ) * Real.log 2 +
      (b : ℝ) * Real.log 5 + (c : ℝ) * Real.log 13 = 0 := by
    push_cast
    nlinarith [hscaled]
  obtain ⟨ha, hb, hc⟩ := two_five_thirteen_integer_log_relation (a - 3*c) b c hrelation
  exact ⟨by omega, hb, hc⟩

theorem wheatstone_three_dimensions_independent :
    LinearIndependent ℚ ![(1 : ℝ), Real.log 5 / Real.log 2,
      Real.log (13 / 8) / Real.log 2] := by
  have hinteger : LinearIndependent ℤ ![(1 : ℝ), Real.log 5 / Real.log 2,
      Real.log (13 / 8) / Real.log 2] := by
    rw [Fintype.linearIndependent_iff]
    intro coefficients hrelation index
    have h : (coefficients 0 : ℝ) + (coefficients 1 : ℝ) * (Real.log 5 / Real.log 2) +
        (coefficients 2 : ℝ) * (Real.log (13 / 8) / Real.log 2) = 0 := by
      simpa [Fin.sum_univ_succ, zsmul_eq_mul, add_assoc] using hrelation
    obtain ⟨h0, h1, h2⟩ := wheatstone_integer_dimension_relation _ _ _ h
    fin_cases index <;> assumption
  exact hinteger.localization ℚ (nonZeroDivisors ℤ)

/-- The pivotal multiplier in the independent triple is the derivative of
the actual Wheatstone crossing function at its unique interior fixed point. -/
theorem wheatstone_actual_pivotal_independent :
    LinearIndependent ℚ ![(1 : ℝ), Real.log 5 / Real.log 2,
      Real.log (deriv wheatstoneNetwork.reliability (1 / 2)) / Real.log 2] := by
  rw [wheatstone_deriv_half]
  exact wheatstone_three_dimensions_independent

/-- Arithmetic form of the whole-class Wheatstone conclusion. Graph
algebraicity supplies the displayed algebraic exponentials for any other
representative sharing these two dimensions. -/
theorem wheatstone_scale_is_power_two (scale : ℕ) (hscale : 1 < scale)
    (halgebraic : ∀ index : Fin 3, IsAlgebraic ℚ
      (Real.exp (Real.log (scale : ℝ) *
        (![1, Real.log 5 / Real.log 2, Real.log (13 / 8) / Real.log 2] index)))) :
    ∃ exponent : ℕ, 0 < exponent ∧ scale = 2 ^ exponent := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hfirst : ∀ index : Fin 3, IsAlgebraic ℚ
      (Real.exp (Real.log (2 : ℝ) *
        (![1, Real.log 5 / Real.log 2, Real.log (13 / 8) / Real.log 2] index))) := by
    intro index
    fin_cases index
    · change IsAlgebraic ℚ (Real.exp (Real.log (2 : ℝ) * 1))
      rw [mul_one, Real.exp_log (by norm_num)]
      exact isAlgebraic_nat 2
    · change IsAlgebraic ℚ (Real.exp (Real.log (2 : ℝ) * (Real.log 5 / Real.log 2)))
      rw [mul_comm, div_mul_cancel₀ _ hlog2, Real.exp_log (by norm_num)]
      exact isAlgebraic_nat 5
    · change IsAlgebraic ℚ (Real.exp (Real.log (2 : ℝ) * (Real.log (13 / 8) / Real.log 2)))
      rw [mul_comm, div_mul_cancel₀ _ hlog2, Real.exp_log (by norm_num)]
      simpa only [map_div₀, map_ofNat] using
        (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (13 / 8))
  have hcommensurate := commensurate_of_three_independent_dimensions (by norm_num : 1 < (2 : ℕ))
    hscale _ wheatstone_three_dimensions_independent hfirst halgebraic
  apply (commensurate_with_primitive_base_iff (base := 2) ?_ hscale).mp hcommensurate
  refine ⟨by norm_num, ?_⟩
  intro root exponent hexponent hpower
  have hpow := Nat.Prime.pow_eq_iff Nat.prime_two |>.mp hpower.symm
  omega

end Universality.Section4

#print axioms Universality.Section4.two_five_thirteen_integer_log_relation
#print axioms Universality.Section4.wheatstone_three_dimensions_independent
#print axioms Universality.Section4.wheatstone_actual_pivotal_independent
#print axioms Universality.Section4.wheatstone_scale_is_power_two
