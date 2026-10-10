import Universality.Probability.FiniteWeightSquare
import Mathlib.Analysis.MeanInequalities

namespace Universality
noncomputable section

/-- Jensen followed by finite-sum Holder, with a uniform bound on the number
of objects in each random finite family. No independence is required. -/
theorem finite_random_family_moment {Outcome Object : Type*} [Fintype Outcome]
    (weight : Outcome → ℝ) (family : Outcome → Finset Object) (value : Outcome → Object → ℝ)
    (hnonneg : ∀ outcome, 0 ≤ weight outcome) (hsum : ∑ outcome, weight outcome = 1)
    (hvalue : ∀ outcome object, object ∈ family outcome → 0 ≤ value outcome object)
    (bound : ℕ) (hcard : ∀ outcome, (family outcome).card ≤ bound)
    (order : ℕ) (horder : 1 ≤ order) :
    (∑ outcome, weight outcome * ∑ object ∈ family outcome, value outcome object) ^ order ≤
      (bound : ℝ) ^ (order - 1) *
        ∑ outcome, weight outcome * ∑ object ∈ family outcome, value outcome object ^ order := by
  have hjensen := finite_weighted_mean_pow_le weight
    (fun outcome => ∑ object ∈ family outcome, value outcome object)
    hnonneg hsum (fun outcome => Finset.sum_nonneg (fun object hobject => hvalue outcome object hobject)) order
  apply hjensen.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro outcome _
  have hholder : (∑ object ∈ family outcome, value outcome object) ^ order ≤
      ((family outcome).card : ℝ) ^ (order - 1) *
        ∑ object ∈ family outcome, value outcome object ^ order := by
    have hr := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (family outcome) (f := value outcome)
      (p := (order : ℝ)) (by exact_mod_cast horder) (hvalue outcome)
    have hcast : ((order - 1 : ℕ) : ℝ) = (order : ℝ) - 1 := by
      rw [Nat.cast_sub horder, Nat.cast_one]
    simpa only [← hcast, Real.rpow_natCast] using hr
  have hbound : ((family outcome).card : ℝ) ^ (order - 1) ≤ (bound : ℝ) ^ (order - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcard outcome) _
  have hpoint := hholder.trans (mul_le_mul_of_nonneg_right hbound
    (Finset.sum_nonneg (fun object hobject => pow_nonneg (hvalue outcome object hobject) _)))
  simpa only [mul_assoc, mul_left_comm (weight outcome) ((bound : ℝ) ^ (order - 1))] using
    mul_le_mul_of_nonneg_left hpoint (hnonneg outcome)

end
end Universality
