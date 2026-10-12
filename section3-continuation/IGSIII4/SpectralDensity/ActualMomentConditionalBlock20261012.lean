import IGSIII4.SpectralDensity.ActualMomentBlockLaw20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability
attribute [local instance] Classical.propDecidable
variable {Path Outcome : Type*} [Fintype Path] [DecidableEq Path]
  [Fintype Outcome] [Nonempty Outcome] {length : ℕ}

def conditionalBlockObservable (statusWeight : (Path → Bool) → ℝ)
    (weight response : Outcome → ℝ) (observable : ℝ → ℝ) : ℝ :=
  finiteMean statusWeight (fun success => finiteMean (blockProductWeight weight)
    (fun input : Path → Fin length → Outcome => observable (blockInputResponse success response input)))

theorem conditionalBlock_second_moment20261012
    (statusWeight : (Path → Bool) → ℝ)
    (statusNonnegative : ∀ success, 0 ≤ statusWeight success)
    (statusNormalized : ∑ success, statusWeight success = 1)
    (noEmpty : ∀ success, (¬∃ path, success path = true) → statusWeight success = 0)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    conditionalBlockObservable (length := length) statusWeight weight response (fun value => value ^ 2) ≤
      (length : ℝ) ^ 2 + 8 * length := by
  have comparison : conditionalBlockObservable (length := length) statusWeight weight response (fun value => value ^ 2) ≤
      finiteMean statusWeight (fun _ => (length : ℝ) ^ 2 + 8 * length) := by
    apply Finset.sum_le_sum
    intro success _
    by_cases crosses : ∃ path, success path = true
    · exact mul_le_mul_of_nonneg_left
        (finiteMean_block_second_moment20261012 success crosses weight response weightNonnegative
          normalized positive lengthPositive meanOne varianceBound) (statusNonnegative success)
    · simp only [noEmpty success crosses, zero_mul, le_refl]
  exact comparison.trans_eq (finiteMean_const statusWeight statusNormalized _)

theorem conditionalBlock_mean_lower20261012
    (statusWeight : (Path → Bool) → ℝ)
    (statusNonnegative : ∀ success, 0 ≤ statusWeight success)
    (statusNormalized : ∑ success, statusWeight success = 1)
    (noEmpty : ∀ success, (¬∃ path, success path = true) → statusWeight success = 0)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    (length : ℝ) / 2 * finiteMean statusWeight (fun success => 1 / successfulPathCount success) -
        (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length ≤
      conditionalBlockObservable (length := length) statusWeight weight response id := by
  have comparison : finiteMean statusWeight (fun success =>
      (length : ℝ) / 2 / successfulPathCount success - (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length) ≤
      conditionalBlockObservable (length := length) statusWeight weight response id := by
    apply Finset.sum_le_sum
    intro success _
    by_cases crosses : ∃ path, success path = true
    · exact mul_le_mul_of_nonneg_left
        (finiteMean_block_lower20261012 success crosses weight response weightNonnegative
          normalized positive lengthPositive meanOne varianceBound) (statusNonnegative success)
    · simp only [noEmpty success crosses, zero_mul, le_refl]
  have average : finiteMean statusWeight (fun success =>
      (length : ℝ) / 2 / successfulPathCount success - (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length) =
      (length : ℝ) / 2 * finiteMean statusWeight (fun success => 1 / successfulPathCount success) -
        (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length := by
    simp only [finiteMean, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, statusNormalized, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro success _
    ring
  rwa [average] at comparison

end
end IGSIII4.SpectralDensity
