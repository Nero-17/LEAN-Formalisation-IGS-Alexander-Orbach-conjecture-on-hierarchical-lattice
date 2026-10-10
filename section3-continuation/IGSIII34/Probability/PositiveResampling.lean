import IGSIII34.Probability.ResamplingSymmetry
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace IGSIII34.Probability
noncomputable section
open scoped BigOperators
variable {Outcome : Type*} [Fintype Outcome] {count : ℕ}

theorem finiteMean_fintypeSum {Index : Type*} [Fintype Index]
    (weight : Outcome → ℝ) (response : Index → Outcome → ℝ) :
    finiteMean weight (fun outcome => ∑ index, response index outcome) =
      ∑ index, finiteMean weight (response index) := by
  simp only [finiteMean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem square_eq_positive_parts (first second : ℝ) :
    (first - second) ^ 2 = max (second - first) 0 ^ 2 + max (first - second) 0 ^ 2 := by
  rcases le_total first second with comparison | comparison
  · rw [max_eq_left (sub_nonneg.mpr comparison), max_eq_right (sub_nonpos.mpr comparison)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr comparison), max_eq_left (sub_nonneg.mpr comparison)]
    ring

def positiveResamplingEnergy (weight : Fin count → Outcome → ℝ)
    (response : (Fin count → Outcome) → ℝ) : ℝ :=
  finiteMean (tupleWeight weight) (fun outcome => ∑ coordinate,
    finiteMean (weight coordinate) (fun replacement =>
      max (response (Function.update outcome coordinate replacement) - response outcome) 0 ^ 2))

theorem resamplingEnergy_eq_two_positive (weight : Fin count → Outcome → ℝ)
    (response : (Fin count → Outcome) → ℝ) :
    resamplingEnergy weight response = 2 * positiveResamplingEnergy weight response := by
  have exchange (coordinate : Fin count) :
      finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight coordinate) (fun replacement =>
        max (response outcome - response (Function.update outcome coordinate replacement)) 0 ^ 2)) =
      finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight coordinate) (fun replacement =>
        max (response (Function.update outcome coordinate replacement) - response outcome) 0 ^ 2)) := by
    rw [← finiteMean_product, ← finiteMean_product]
    rw [finiteMean_resampling_exchange weight coordinate]
    apply Finset.sum_congr rfl
    intro pair _
    congr 2
    change max (response (Function.update pair.1 coordinate pair.2) -
      response (Function.update (Function.update pair.1 coordinate pair.2) coordinate (pair.1 coordinate))) 0 ^ 2 = _
    simp only [Function.update_idem, Function.update_eq_self]
  have negativeEquals :
      (finiteMean (tupleWeight weight) (fun outcome => ∑ coordinate,
        finiteMean (weight coordinate) (fun replacement =>
          max (response outcome - response (Function.update outcome coordinate replacement)) 0 ^ 2))) =
      positiveResamplingEnergy weight response := by
    unfold positiveResamplingEnergy
    rw [finiteMean_fintypeSum, finiteMean_fintypeSum]
    apply Finset.sum_congr rfl
    intro coordinate _
    exact exchange coordinate
  have decomposition : resamplingEnergy weight response =
      positiveResamplingEnergy weight response +
      finiteMean (tupleWeight weight) (fun outcome => ∑ coordinate,
        finiteMean (weight coordinate) (fun replacement =>
          max (response outcome - response (Function.update outcome coordinate replacement)) 0 ^ 2)) := by
    unfold resamplingEnergy positiveResamplingEnergy finiteMean
    simp_rw [square_eq_positive_parts, mul_add, Finset.sum_add_distrib]
    simp only [mul_add, Finset.sum_add_distrib]
  rw [decomposition, negativeEquals]
  ring

theorem finite_product_variance_le_positive_resampling (count : ℕ)
    (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    finiteVariance (tupleWeight weight) response ≤ 2 * positiveResamplingEnergy weight response :=
  (finite_product_variance_le_resampling count weight nonnegative normalized response).trans_eq
    (resamplingEnergy_eq_two_positive weight response)

end
end IGSIII34.Probability
