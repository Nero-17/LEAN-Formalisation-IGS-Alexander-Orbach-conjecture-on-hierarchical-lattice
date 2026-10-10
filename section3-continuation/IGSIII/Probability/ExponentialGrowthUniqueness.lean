import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace IGSIII.Probability

theorem le_of_powers_bounded_by_multiple
    (first second coefficient : ℝ) (secondPositive : 0 < second)
    (bounds : ∀ depth : ℕ, first ^ depth ≤ coefficient * second ^ depth) : first ≤ second := by
  by_contra failure
  have ratioGreaterThanOne : 1 < first / second := (one_lt_div secondPositive).mpr (lt_of_not_ge failure)
  obtain ⟨depth, exceeds⟩ := pow_unbounded_of_one_lt coefficient ratioGreaterThanOne
  have bound : (first / second) ^ depth ≤ coefficient := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos secondPositive depth)).mpr (bounds depth)
  exact (not_lt_of_ge bound) exceeds

theorem exponential_growth_unique (sequence : ℕ → ℝ)
    (first second firstCoefficient secondCoefficient : ℝ)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (firstBounds : ∀ depth, first ^ depth ≤ sequence depth ∧ sequence depth ≤ firstCoefficient * first ^ depth)
    (secondBounds : ∀ depth, second ^ depth ≤ sequence depth ∧ sequence depth ≤ secondCoefficient * second ^ depth) :
    first = second := by
  apply le_antisymm
  · exact le_of_powers_bounded_by_multiple first second secondCoefficient secondPositive
      (fun depth => (firstBounds depth).1.trans (secondBounds depth).2)
  · exact le_of_powers_bounded_by_multiple second first firstCoefficient firstPositive
      (fun depth => (secondBounds depth).1.trans (firstBounds depth).2)

end IGSIII.Probability
