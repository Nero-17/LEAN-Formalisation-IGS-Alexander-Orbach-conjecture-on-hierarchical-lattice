import Universality.Arithmetic.NoIntegerPower
import Mathlib.RingTheory.Localization.Module
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Logarithmic independence from nonsplitting of the mass multiplier

The integer relation first forces a power of the mass multiplier into the
coefficient field. Its exponent vanishes by nonsplitting; the remaining pair
is independent because no positive power of the pivotal multiplier is an
integer. Scalar localization then gives rational linear independence.
-/

namespace Universality.Section4
noncomputable section

theorem integer_log_relation_of_mass_power_not_mem
    (field : Subfield ℝ) (base : ℕ) (multiplier mass : ℝ)
    (hbase : 1 < base) (hmultiplier : 1 < multiplier) (hmass : 0 < mass)
    (hmultiplier_mem : multiplier ∈ field)
    (hno_integer_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, multiplier ^ exponent ≠ integer)
    (hmass_power : ∀ exponent : ℤ, exponent ≠ 0 → mass ^ exponent ∉ field)
    (a b c : ℤ)
    (hrelation : (a : ℝ) * Real.log (base : ℝ) +
      (b : ℝ) * Real.log multiplier + (c : ℝ) * Real.log mass = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hbase_positive : (0 : ℝ) < base := by exact_mod_cast (lt_trans Nat.zero_lt_one hbase)
  have hmultiplier_positive : 0 < multiplier := lt_trans zero_lt_one hmultiplier
  have hproduct : (base : ℝ) ^ a * multiplier ^ b * mass ^ c = 1 := by
    apply Real.log_injOn_pos
      (mul_pos (mul_pos (zpow_pos hbase_positive a) (zpow_pos hmultiplier_positive b))
        (zpow_pos hmass c)) (by norm_num : (0 : ℝ) < 1)
    rw [Real.log_mul (mul_ne_zero (zpow_ne_zero a hbase_positive.ne')
        (zpow_ne_zero b hmultiplier_positive.ne')) (zpow_ne_zero c hmass.ne'),
      Real.log_mul (zpow_ne_zero a hbase_positive.ne')
        (zpow_ne_zero b hmultiplier_positive.ne'),
      Real.log_zpow, Real.log_zpow, Real.log_zpow, Real.log_one]
    exact hrelation
  have hmass_member : mass ^ c ∈ field := by
    rw [eq_inv_of_mul_eq_one_right hproduct]
    exact field.inv_mem (field.mul_mem (field.zpow_mem (natCast_mem field base) a)
      (field.zpow_mem hmultiplier_mem b))
  have hc : c = 0 := by
    by_contra hnonzero
    exact hmass_power c hnonzero hmass_member
  have hpair : LinearIndependent ℤ ![Real.log (base : ℝ), Real.log multiplier] :=
    (linearIndependent_logs_of_no_integer_power base multiplier hbase hmultiplier
      hno_integer_power).restrict_scalars' ℤ
  have hsum : ∑ index : Fin 2, (![a, b] index) •
      (![Real.log (base : ℝ), Real.log multiplier] index) = 0 := by
    simpa [hc, Fin.sum_univ_succ, zsmul_eq_mul, add_assoc] using hrelation
  have hcoefficients := Fintype.linearIndependent_iff.mp hpair ![a, b] hsum
  exact ⟨hcoefficients 0, hcoefficients 1, hc⟩

theorem logarithmic_dimensions_independent_of_mass_power_not_mem
    (field : Subfield ℝ) (base scale : ℕ) (multiplier mass : ℝ)
    (hbase : 1 < base) (hscale : 1 < scale)
    (hmultiplier : 1 < multiplier) (hmass : 0 < mass)
    (hmultiplier_mem : multiplier ∈ field)
    (hno_integer_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, multiplier ^ exponent ≠ integer)
    (hmass_power : ∀ exponent : ℤ, exponent ≠ 0 → mass ^ exponent ∉ field) :
    LinearIndependent ℚ ![Real.log (base : ℝ) / Real.log (scale : ℝ),
      Real.log mass / Real.log (scale : ℝ), Real.log multiplier / Real.log (scale : ℝ)] := by
  have hlog_scale : Real.log (scale : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hscale))
  have hinteger : LinearIndependent ℤ ![Real.log (base : ℝ) / Real.log (scale : ℝ),
      Real.log mass / Real.log (scale : ℝ), Real.log multiplier / Real.log (scale : ℝ)] := by
    rw [Fintype.linearIndependent_iff]
    intro coefficients hrelation index
    have hsum : (coefficients 0 : ℝ) * (Real.log (base : ℝ) / Real.log (scale : ℝ)) +
        (coefficients 1 : ℝ) * (Real.log mass / Real.log (scale : ℝ)) +
        (coefficients 2 : ℝ) * (Real.log multiplier / Real.log (scale : ℝ)) = 0 := by
      simpa [Fin.sum_univ_succ, zsmul_eq_mul, add_assoc] using hrelation
    have hscaled := congrArg (fun value : ℝ => value * Real.log (scale : ℝ)) hsum
    simp only [add_mul, mul_assoc, div_mul_cancel₀ _ hlog_scale, zero_mul] at hscaled
    have hlog_relation : (coefficients 0 : ℝ) * Real.log (base : ℝ) +
        (coefficients 2 : ℝ) * Real.log multiplier +
        (coefficients 1 : ℝ) * Real.log mass = 0 := by linarith
    obtain ⟨h0, h2, h1⟩ := integer_log_relation_of_mass_power_not_mem field base multiplier mass
      hbase hmultiplier hmass hmultiplier_mem hno_integer_power hmass_power
      (coefficients 0) (coefficients 2) (coefficients 1) hlog_relation
    fin_cases index <;> assumption
  exact hinteger.localization ℚ (nonZeroDivisors ℤ)

end
end Universality.Section4

#print axioms Universality.Section4.integer_log_relation_of_mass_power_not_mem
#print axioms Universality.Section4.logarithmic_dimensions_independent_of_mass_power_not_mem
