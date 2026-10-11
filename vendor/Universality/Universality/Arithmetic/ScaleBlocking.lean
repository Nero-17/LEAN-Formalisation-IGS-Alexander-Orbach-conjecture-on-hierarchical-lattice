import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Independent Section 4 feasibility probe. Only mathlib is imported.
These lemmas concern logarithmic growth data, not the existence of physical
critical exponents or the six exponentials theorem.
-/

namespace Universality.Section4

theorem normalized_log_pow (scale multiplier : ℝ) (steps : ℕ)
    (hsteps : 0 < steps) :
    Real.log (multiplier ^ steps) / Real.log (scale ^ steps) =
      Real.log multiplier / Real.log scale := by
  rw [Real.log_pow, Real.log_pow]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsteps))

theorem aligned_log_dimensions_iff
    (scale₁ scale₂ multiplier₁ multiplier₂ : ℝ) (steps₁ steps₂ : ℕ)
    (hscale₂ : 1 < scale₂)
    (hmultiplier₁ : 0 < multiplier₁) (hmultiplier₂ : 0 < multiplier₂)
    (hsteps₁ : 0 < steps₁) (hsteps₂ : 0 < steps₂)
    (haligned : scale₁ ^ steps₁ = scale₂ ^ steps₂) :
    Real.log multiplier₁ / Real.log scale₁ =
        Real.log multiplier₂ / Real.log scale₂ ↔
      multiplier₁ ^ steps₁ = multiplier₂ ^ steps₂ := by
  have hdenominator : Real.log (scale₂ ^ steps₂) ≠ 0 := by
    rw [Real.log_pow]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hsteps₂))
      (ne_of_gt (Real.log_pos hscale₂))
  rw [← normalized_log_pow scale₁ multiplier₁ steps₁ hsteps₁,
    ← normalized_log_pow scale₂ multiplier₂ steps₂ hsteps₂,
    haligned, div_left_inj' hdenominator]
  constructor
  · exact Real.log_injOn_pos (pow_pos hmultiplier₁ _) (pow_pos hmultiplier₂ _)
  · exact congrArg Real.log

end Universality.Section4

#print axioms Universality.Section4.normalized_log_pow
#print axioms Universality.Section4.aligned_log_dimensions_iff
