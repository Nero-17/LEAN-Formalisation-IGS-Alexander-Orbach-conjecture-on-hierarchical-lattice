import Universality.Probability.FiniteRandomFamilyMoment

namespace Universality
noncomputable section

/-- A random family supported on a rare event obeys a second-moment bound
with the event's expected dominating indicator. No independence is assumed. -/
theorem finite_random_family_rare_square {Outcome Object : Type*} [Fintype Outcome]
    (weight failure : Outcome → ℝ) (family : Outcome → Finset Object)
    (value : Outcome → Object → ℝ) (bound : ℕ)
    (hweight : ∀ outcome, 0 ≤ weight outcome) (hfailure : ∀ outcome, 0 ≤ failure outcome)
    (hcard : ∀ outcome, (family outcome).card ≤ bound)
    (hsupport : ∀ outcome, (family outcome).Nonempty → 1 ≤ failure outcome) :
    (∑ outcome, weight outcome * ∑ object ∈ family outcome, value outcome object) ^ 2 ≤
      (bound : ℝ) * (∑ outcome, weight outcome * failure outcome) *
        ∑ outcome, weight outcome * ∑ object ∈ family outcome, value outcome object ^ 2 := by
  have hpoint (outcome : Outcome) :
      (∑ object ∈ family outcome, value outcome object) ^ 2 ≤
        failure outcome * ((bound : ℝ) * ∑ object ∈ family outcome, value outcome object ^ 2) := by
    by_cases hempty : family outcome = ∅
    · simp [hempty]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (family outcome) (fun _ => (1 : ℝ)) (value outcome)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hbound := hcs.trans (mul_le_mul_of_nonneg_right
      (show ((family outcome).card : ℝ) ≤ (bound : ℝ) by exact_mod_cast hcard outcome) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    exact hbound.trans (le_mul_of_one_le_left
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (hsupport outcome (Finset.nonempty_iff_ne_empty.mpr hempty)))
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun outcome => weight outcome * ∑ object ∈ family outcome, value outcome object)
    (f := fun outcome => weight outcome * failure outcome)
    (g := fun outcome => weight outcome * ((bound : ℝ) * ∑ object ∈ family outcome, value outcome object ^ 2))
    (fun outcome _ => mul_nonneg (hweight outcome) (hfailure outcome))
    (fun outcome _ => mul_nonneg (hweight outcome)
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
    (by
      intro outcome _
      have hh := mul_le_mul_of_nonneg_left (hpoint outcome) (sq_nonneg (weight outcome))
      nlinarith only [hh])
  calc
    _ ≤ _ := hcs
    _ = _ := by
      simp_rw [mul_left_comm (weight _) (bound : ℝ), ← Finset.mul_sum]
      ring

end
end Universality
