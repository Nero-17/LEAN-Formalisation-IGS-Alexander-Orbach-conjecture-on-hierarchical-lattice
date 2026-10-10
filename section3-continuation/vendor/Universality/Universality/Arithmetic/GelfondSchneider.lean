import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Accepted external Gelfond--Schneider theorem

The positive-real-base form of the standard theorem used in Section 4.
The user explicitly accepted this external theorem on 2026-10-06.
The exponential expression fixes the real branch of the power.
-/

namespace Universality.External

axiom gelfond_schneider_real (base exponent : ℝ)
    (hbase : 0 < base) (hbase_one : base ≠ 1)
    (hbase_algebraic : IsAlgebraic ℚ base)
    (hexponent_algebraic : IsAlgebraic ℚ exponent)
    (hexponent_irrational : Irrational exponent) :
    Transcendental ℚ (Real.exp (exponent * Real.log base))

end Universality.External

namespace Universality.Section4

theorem logarithmic_dimension_transcendental
    (base multiplier : ℝ) (hbase : 1 < base) (hmultiplier : 0 < multiplier)
    (hbase_algebraic : IsAlgebraic ℚ base)
    (hmultiplier_algebraic : IsAlgebraic ℚ multiplier)
    (hirrational : Irrational (Real.log multiplier / Real.log base)) :
    Transcendental ℚ (Real.log multiplier / Real.log base) := by
  intro halgebraic
  have htranscendental := External.gelfond_schneider_real base
    (Real.log multiplier / Real.log base) (lt_trans zero_lt_one hbase)
    (ne_of_gt hbase) hbase_algebraic halgebraic hirrational
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hbase)),
    Real.exp_log hmultiplier] at htranscendental
  exact htranscendental hmultiplier_algebraic

end Universality.Section4

#print axioms Universality.Section4.logarithmic_dimension_transcendental
