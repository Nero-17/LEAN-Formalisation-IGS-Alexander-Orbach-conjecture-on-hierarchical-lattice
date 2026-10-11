import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The three exact scale logarithms in Section 5.
The valuation proof follows the generic argument used in the independently
formalised Section 4 Wheatstone arithmetic, with its three prime bases replaced.
-/
namespace Universality.Section5
private theorem prime_valuation_product (prime : ℕ) [Fact prime.Prime]
    (a b c : ℤ) :
    padicValRat prime ((19 : ℚ) ^ a * 661 ^ b * 739 ^ c) =
      a * padicValRat prime 19 + b * padicValRat prime 661 + c * padicValRat prime 739 := by
  rw [padicValRat.mul (mul_ne_zero (zpow_ne_zero a (by norm_num))
      (zpow_ne_zero b (by norm_num))) (zpow_ne_zero c (by norm_num)),
    padicValRat.mul (zpow_ne_zero a (by norm_num)) (zpow_ne_zero b (by norm_num))]
  simp

theorem nineteen_661_739_zpow_independent (a b c : ℤ)
    (h : (19 : ℚ) ^ a * 661 ^ b * 739 ^ c = 1) : a = 0 ∧ b = 0 ∧ c = 0 := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 661) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 739) := ⟨by norm_num⟩
  have h2 := congrArg (padicValRat 19) h
  have h5 := congrArg (padicValRat 661) h
  have h13 := congrArg (padicValRat 739) h
  rw [prime_valuation_product] at h2 h5 h13
  have h25 : padicValNat 19 661 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h213 : padicValNat 19 739 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h52 : padicValNat 661 19 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h513 : padicValNat 661 739 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h132 : padicValNat 739 19 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have h135 : padicValNat 739 661 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  norm_num [padicValRat, padicValInt, h25, h213, h52, h513, h132, h135] at h2 h5 h13
  exact ⟨h2, h5, h13⟩

theorem nineteen_661_739_integer_log_relation (a b c : ℤ)
    (h : (a : ℝ) * Real.log 19 + (b : ℝ) * Real.log 661 +
      (c : ℝ) * Real.log 739 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hreal : (19 : ℝ) ^ a * 661 ^ b * 739 ^ c = 1 := by
    apply Real.log_injOn_pos
      (show 0 < (19 : ℝ) ^ a * 661 ^ b * 739 ^ c by positivity)
      (show 0 < (1 : ℝ) by norm_num)
    rw [Real.log_mul (mul_ne_zero (zpow_ne_zero a (by norm_num))
        (zpow_ne_zero b (by norm_num))) (zpow_ne_zero c (by norm_num)),
      Real.log_mul (zpow_ne_zero a (by norm_num)) (zpow_ne_zero b (by norm_num)),
      Real.log_zpow, Real.log_zpow, Real.log_zpow, Real.log_one]
    exact h
  apply nineteen_661_739_zpow_independent a b c
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_one] using hreal

theorem three_scale_logs_independent :
    LinearIndependent ℚ ![Real.log 19, Real.log 661, Real.log 739] := by
  have integer_independent :
      LinearIndependent ℤ ![Real.log 19, Real.log 661, Real.log 739] := by
    rw [Fintype.linearIndependent_iff]
    intro coefficients relation index
    have integer_relation : (coefficients 0 : ℝ) * Real.log 19 +
        (coefficients 1 : ℝ) * Real.log 661 + (coefficients 2 : ℝ) * Real.log 739 = 0 := by
      simpa [Fin.sum_univ_succ, zsmul_eq_mul, add_assoc] using relation
    obtain ⟨first, second, third⟩ := nineteen_661_739_integer_log_relation _ _ _ integer_relation
    fin_cases index <;> assumption
  exact integer_independent.localization ℚ (nonZeroDivisors ℤ)

theorem three_actual_scale_logs_independent :
    LinearIndependent ℚ
      ![Real.log ((19 : ℝ) ^ 100), Real.log ((661 : ℝ) ^ 100), Real.log ((739 : ℝ) ^ 100)] := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients relation index
  apply Fintype.linearIndependent_iff.mp three_scale_logs_independent coefficients ?_ index
  simp only [Real.log_pow] at relation
  simp [Fin.sum_univ_succ, Rat.smul_def, add_assoc] at relation ⊢
  nlinarith

end Universality.Section5
