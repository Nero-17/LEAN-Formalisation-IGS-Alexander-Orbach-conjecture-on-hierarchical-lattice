import Universality.Arithmetic.GelfondSchneider
import Universality.Arithmetic.SixExponentialsReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Universality.Section4

theorem logarithmic_dimension_irrational_of_no_integer_power
    (base : ℕ) (multiplier : ℝ) (hbase : 1 < base) (hmultiplier : 1 < multiplier)
    (hno_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, multiplier ^ exponent ≠ integer) :
    Irrational (Real.log multiplier / Real.log (base : ℝ)) := by
  rintro ⟨coefficient, hcoefficient⟩
  have hbase_real : 1 < (base : ℝ) := by exact_mod_cast hbase
  have hcoefficient_pos : 0 < coefficient := by
    have hpos : (0 : ℝ) < coefficient := by
      rw [hcoefficient]
      exact div_pos (Real.log_pos hmultiplier) (Real.log_pos hbase_real)
    exact_mod_cast hpos
  have hnum_pos : 0 < coefficient.num := Rat.num_pos.mpr hcoefficient_pos
  have hnum_cast : (coefficient.num.natAbs : ℝ) = (coefficient.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun integer : ℤ => (integer : ℝ))
      (Int.natAbs_of_nonneg hnum_pos.le)
  have hden_ne : (coefficient.den : ℝ) ≠ 0 := by exact_mod_cast coefficient.den_ne_zero
  have hlog_ne : Real.log (base : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hbase_real)
  have hratio : Real.log multiplier / Real.log (base : ℝ) =
      (coefficient.num.natAbs : ℝ) / coefficient.den := by
    rw [← hcoefficient, Rat.cast_def, hnum_cast]
  have hlogs := (div_eq_div_iff hlog_ne hden_ne).mp hratio
  have hpowers : multiplier ^ coefficient.den = (base : ℝ) ^ coefficient.num.natAbs := by
    apply Real.log_injOn_pos (pow_pos (lt_trans zero_lt_one hmultiplier) _)
      (pow_pos (lt_trans zero_lt_one hbase_real) _)
    rw [Real.log_pow, Real.log_pow]
    nlinarith
  apply hno_power coefficient.den coefficient.den_pos (base ^ coefficient.num.natAbs)
  simpa only [Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using hpowers

theorem logarithmic_dimension_transcendental_of_no_integer_power
    (base : ℕ) (multiplier : ℝ) (hbase : 1 < base) (hmultiplier : 1 < multiplier)
    (halgebraic : IsAlgebraic ℚ multiplier)
    (hno_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, multiplier ^ exponent ≠ integer) :
    Transcendental ℚ (Real.log multiplier / Real.log (base : ℝ)) := by
  apply logarithmic_dimension_transcendental (base : ℝ) multiplier
    (by exact_mod_cast hbase) (lt_trans zero_lt_one hmultiplier)
    (by simpa using (isAlgebraic_algebraMap (A := ℝ) (base : ℚ))) halgebraic
  exact logarithmic_dimension_irrational_of_no_integer_power base multiplier hbase hmultiplier hno_power

theorem linearIndependent_logs_of_no_integer_power
    (base : ℕ) (multiplier : ℝ) (hbase : 1 < base) (hmultiplier : 1 < multiplier)
    (hno_power : ∀ exponent : ℕ, 0 < exponent →
      ∀ integer : ℤ, multiplier ^ exponent ≠ integer) :
    LinearIndependent ℚ ![Real.log (base : ℝ), Real.log multiplier] := by
  have hlog_ne : Real.log (base : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hbase))
  apply (LinearIndependent.pair_iff' hlog_ne).mpr
  intro coefficient heq
  apply logarithmic_dimension_irrational_of_no_integer_power base multiplier hbase hmultiplier hno_power
  refine ⟨coefficient, ?_⟩
  change (coefficient : ℝ) * Real.log (base : ℝ) = Real.log multiplier at heq
  rw [← heq, mul_div_cancel_right₀ _ hlog_ne]

end Universality.Section4

#print axioms Universality.Section4.logarithmic_dimension_irrational_of_no_integer_power
#print axioms Universality.Section4.logarithmic_dimension_transcendental_of_no_integer_power
