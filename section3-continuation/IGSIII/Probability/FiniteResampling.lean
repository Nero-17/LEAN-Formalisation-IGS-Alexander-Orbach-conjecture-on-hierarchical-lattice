import IGSIII.Probability.FiniteProductTensorization

/-!
# Finite Efron--Stein resampling bound

We use a nonoptimal constant one, which suffices for the geometric decay
estimates in the chemical scalar theorem. Both the variance and resampling
energy are actual finite weighted sums.
-/

set_option autoImplicit false

namespace IGSIII.Probability

open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome]

theorem finiteMean_square_about_constant (weight response : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) (center : ℝ) :
    finiteMean weight (fun outcome => (response outcome - center) ^ 2) =
      finiteVariance weight response + (finiteMean weight response - center) ^ 2 := by
  calc
    _ = ∑ outcome, (weight outcome * response outcome ^ 2 -
          2 * center * (weight outcome * response outcome) + weight outcome * center ^ 2) := by
      apply Finset.sum_congr rfl
      intro outcome _
      ring
    _ = finiteMean weight (fun outcome => response outcome ^ 2) -
          2 * center * finiteMean weight response + center ^ 2 := by
      simp only [finiteMean, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, normalized, one_mul]
    _ = _ := by
      rw [finiteVariance_eq_second_moment weight response normalized]
      ring

theorem finiteVariance_le_square_about_constant (weight response : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) (center : ℝ) :
    finiteVariance weight response ≤
      finiteMean weight (fun outcome => (response outcome - center) ^ 2) := by
  rw [finiteMean_square_about_constant weight response normalized center]
  exact le_add_of_nonneg_right (sq_nonneg _)

def resamplingEnergy {count : ℕ} (weight : Fin count → Outcome → ℝ)
    (response : (Fin count → Outcome) → ℝ) : ℝ :=
  finiteMean (tupleWeight weight) (fun outcome => ∑ coordinate,
    finiteMean (weight coordinate) (fun replacement =>
      (response outcome - response (Function.update outcome coordinate replacement)) ^ 2))

theorem sum_coordinate_variances_le_resampling {count : ℕ}
    (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    sumCoordinateVariances weight response ≤ resamplingEnergy weight response := by
  unfold sumCoordinateVariances resamplingEnergy finiteMean
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ (tupleWeight_nonnegative weight nonnegative outcome)
  apply Finset.sum_le_sum
  intro coordinate _
  have bound := finiteVariance_le_square_about_constant (weight coordinate)
    (fun replacement => response (Function.update outcome coordinate replacement))
    (normalized coordinate) (response outcome)
  calc
    _ ≤ finiteMean (weight coordinate) (fun replacement =>
        (response (Function.update outcome coordinate replacement) - response outcome) ^ 2) := bound
    _ = _ := by
      unfold finiteMean
      apply Finset.sum_congr rfl
      intro replacement _
      ring

theorem finite_product_variance_le_resampling (count : ℕ)
    (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    finiteVariance (tupleWeight weight) response ≤ resamplingEnergy weight response :=
  (finite_product_variance_le_sum_coordinate_variances count weight nonnegative normalized response).trans
    (sum_coordinate_variances_le_resampling weight nonnegative normalized response)

end IGSIII.Probability
