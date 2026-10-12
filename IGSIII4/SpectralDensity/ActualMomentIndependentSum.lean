import IGSIII34.Probability.FiniteProductTensorization
import IGSIII34.Probability.FiniteProduct

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability

theorem finiteVariance_add_constant {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) (constant : ℝ) :
    finiteVariance weight (fun outcome => response outcome + constant) = finiteVariance weight response := by
  unfold finiteVariance
  rw [finiteMean_add, finiteMean_const weight normalized]
  apply Finset.sum_congr rfl
  intro outcome _
  congr 1
  congr 1
  ring

theorem finiteVariance_product_add {First Second : Type*} [Fintype First] [Fintype Second]
    (firstWeight firstResponse : First → ℝ) (secondWeight secondResponse : Second → ℝ)
    (firstNormalized : ∑ first, firstWeight first = 1)
    (secondNormalized : ∑ second, secondWeight second = 1) :
    finiteVariance (fun outcome : First × Second => firstWeight outcome.1 * secondWeight outcome.2)
      (fun outcome => firstResponse outcome.1 + secondResponse outcome.2) =
        finiteVariance firstWeight firstResponse + finiteVariance secondWeight secondResponse := by
  rw [finiteVariance_product_decomposition firstWeight secondWeight firstNormalized secondNormalized
    (fun first second => firstResponse first + secondResponse second)]
  have inside (first : First) :
      finiteVariance secondWeight (fun second => firstResponse first + secondResponse second) =
        finiteVariance secondWeight secondResponse := by
    simpa only [add_comm] using finiteVariance_add_constant secondWeight secondResponse secondNormalized (firstResponse first)
  simp only [inside, finiteMean_const firstWeight firstNormalized,
    finiteMean_add, finiteMean_const secondWeight secondNormalized]
  rw [finiteVariance_add_constant firstWeight firstResponse firstNormalized]
  ring

/-- Exact variance additivity for a finite independent sum; this is the long
branch variance step for independent conditioned parallel blocks. -/
theorem finiteVariance_independent_sum {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) (count : ℕ) :
    finiteVariance (productWeight (Edge := Fin count) weight)
      (fun input => ∑ coordinate, response (input coordinate)) =
        (count : ℝ) * finiteVariance weight response := by
  induction count with
  | zero => simp [finiteVariance, finiteMean, productWeight]
  | succ count inductionHypothesis =>
    change finiteVariance (tupleWeight (fun _ : Fin (count + 1) => weight)) _ = _
    rw [finiteVariance_tuple_cons (fun _ : Fin (count + 1) => weight) (fun _ => normalized)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [finiteVariance_product_add weight response
      (tupleWeight (fun _ : Fin count => weight)) (fun input => ∑ coordinate, response (input coordinate))
      normalized (tupleWeight_normalized _ (fun _ => normalized))]
    change finiteVariance weight response +
      finiteVariance (productWeight (Edge := Fin count) weight) (fun input => ∑ coordinate, response (input coordinate)) = _
    rw [inductionHypothesis]
    push_cast
    ring

theorem finiteVariance_independent_sum_le_second_moment {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1)
    (count : ℕ) (bound : ℝ)
    (secondMomentBound : finiteMean weight (fun outcome => response outcome ^ 2) ≤ bound) :
    finiteVariance (productWeight (Edge := Fin count) weight)
      (fun input => ∑ coordinate, response (input coordinate)) ≤ (count : ℝ) * bound := by
  rw [finiteVariance_independent_sum weight response normalized,
    finiteVariance_eq_second_moment weight response normalized]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg count)
  linarith [sq_nonneg (finiteMean weight response)]

end
end IGSIII4.SpectralDensity
