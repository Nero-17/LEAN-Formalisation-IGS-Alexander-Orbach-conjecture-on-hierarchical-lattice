import IGSIII34.Probability.FiniteTensorization

/-!
# Tensorization for an arbitrary finite number of coordinates

The recursively computed energy is the sum of the conditional coordinate
variances, averaged over the other independent coordinates. Its definition
uses only finite weights and the response function.
-/

set_option autoImplicit false

namespace IGSIII34.Probability

open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome]

def tupleWeight {count : ℕ} (weight : Fin count → Outcome → ℝ)
    (outcome : Fin count → Outcome) : ℝ :=
  ∏ coordinate, weight coordinate (outcome coordinate)

omit [Fintype Outcome] in
theorem tupleWeight_nonnegative {count : ℕ} (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (outcome : Fin count → Outcome) : 0 ≤ tupleWeight weight outcome :=
  Finset.prod_nonneg (fun coordinate _ => nonnegative coordinate (outcome coordinate))

theorem tupleWeight_normalized {count : ℕ} (weight : Fin count → Outcome → ℝ)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1) :
    ∑ outcome, tupleWeight weight outcome = 1 := by
  unfold tupleWeight
  rw [← Fintype.prod_sum]
  simp only [normalized, Finset.prod_const_one]

theorem finiteMean_tuple_cons {count : ℕ} (weight : Fin (count + 1) → Outcome → ℝ)
    (response : (Fin (count + 1) → Outcome) → ℝ) :
    finiteMean (tupleWeight weight) response =
      finiteMean (weight 0) (fun first =>
        finiteMean (tupleWeight (fun coordinate => weight coordinate.succ))
          (fun rest => response (Fin.cons first rest))) := by
  calc
    _ = ∑ pair : Outcome × (Fin count → Outcome),
        tupleWeight weight (Fin.cons pair.1 pair.2) * response (Fin.cons pair.1 pair.2) :=
      ((Fin.consEquiv (fun _ : Fin (count + 1) => Outcome)).sum_comp
        (fun outcome => tupleWeight weight outcome * response outcome)).symm
    _ = _ := by
      simp only [finiteMean, Fintype.sum_prod_type, tupleWeight, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem finiteVariance_tuple_cons {count : ℕ}
    (weight : Fin (count + 1) → Outcome → ℝ)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin (count + 1) → Outcome) → ℝ) :
    finiteVariance (tupleWeight weight) response =
      finiteVariance
        (fun pair : Outcome × (Fin count → Outcome) =>
          weight 0 pair.1 * tupleWeight (fun coordinate => weight coordinate.succ) pair.2)
        (fun pair => response (Fin.cons pair.1 pair.2)) := by
  rw [finiteVariance_eq_second_moment _ _ (tupleWeight_normalized weight normalized)]
  rw [finiteVariance_eq_second_moment _ _
    (product_weight_normalized (weight 0) (tupleWeight (fun coordinate => weight coordinate.succ))
      (normalized 0) (tupleWeight_normalized _ (fun coordinate => normalized coordinate.succ)))]
  rw [finiteMean_tuple_cons weight (fun outcome => response outcome ^ 2)]
  rw [finiteMean_tuple_cons weight response]
  rw [finiteMean_product (weight 0) (tupleWeight (fun coordinate => weight coordinate.succ))
    (fun first rest => response (Fin.cons first rest) ^ 2)]
  rw [finiteMean_product (weight 0) (tupleWeight (fun coordinate => weight coordinate.succ))
    (fun first rest => response (Fin.cons first rest))]

def coordinateVarianceEnergy : (count : ℕ) →
    (Fin count → Outcome → ℝ) → ((Fin count → Outcome) → ℝ) → ℝ
  | 0, _, _ => 0
  | count + 1, weight, response =>
      finiteMean (weight 0) (fun first =>
        coordinateVarianceEnergy count (fun coordinate => weight coordinate.succ)
          (fun rest => response (Fin.cons first rest))) +
        finiteMean (tupleWeight (fun coordinate => weight coordinate.succ)) (fun rest =>
          finiteVariance (weight 0) (fun first => response (Fin.cons first rest)))

theorem finite_product_variance_le_coordinate_energy (count : ℕ)
    (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    finiteVariance (tupleWeight weight) response ≤ coordinateVarianceEnergy count weight response := by
  induction count with
  | zero =>
      simp [finiteVariance, finiteMean, tupleWeight, coordinateVarianceEnergy]
  | succ count inductionHypothesis =>
      rw [finiteVariance_tuple_cons weight normalized response]
      calc
        _ ≤ finiteMean (weight 0) (fun first =>
            finiteVariance (tupleWeight (fun coordinate => weight coordinate.succ))
              (fun rest => response (Fin.cons first rest))) +
            finiteMean (tupleWeight (fun coordinate => weight coordinate.succ)) (fun rest =>
              finiteVariance (weight 0) (fun first => response (Fin.cons first rest))) :=
          finite_product_variance_tensorization_two_blocks (weight 0)
            (tupleWeight (fun coordinate => weight coordinate.succ))
            (nonnegative 0) (tupleWeight_nonnegative _ (fun coordinate => nonnegative coordinate.succ))
            (normalized 0) (tupleWeight_normalized _ (fun coordinate => normalized coordinate.succ)) _
        _ ≤ coordinateVarianceEnergy (count + 1) weight response := by
          simp only [coordinateVarianceEnergy]
          refine add_le_add ?_ le_rfl
          apply Finset.sum_le_sum
          intro first _
          exact mul_le_mul_of_nonneg_left
            (inductionHypothesis (fun coordinate => weight coordinate.succ)
              (fun coordinate => nonnegative coordinate.succ)
              (fun coordinate => normalized coordinate.succ)
              (fun rest => response (Fin.cons first rest))) (nonnegative 0 first)

def sumCoordinateVariances {count : ℕ} (weight : Fin count → Outcome → ℝ)
    (response : (Fin count → Outcome) → ℝ) : ℝ :=
  finiteMean (tupleWeight weight) (fun outcome =>
    ∑ coordinate, finiteVariance (weight coordinate)
      (fun replacement => response (Function.update outcome coordinate replacement)))

theorem sumCoordinateVariances_cons {count : ℕ}
    (weight : Fin (count + 1) → Outcome → ℝ)
    (normalized : ∑ outcome, weight 0 outcome = 1)
    (response : (Fin (count + 1) → Outcome) → ℝ) :
    sumCoordinateVariances weight response =
      finiteMean (weight 0) (fun first =>
        sumCoordinateVariances (fun coordinate => weight coordinate.succ)
          (fun rest => response (Fin.cons first rest))) +
        finiteMean (tupleWeight (fun coordinate => weight coordinate.succ)) (fun rest =>
          finiteVariance (weight 0) (fun first => response (Fin.cons first rest))) := by
  unfold sumCoordinateVariances
  rw [finiteMean_tuple_cons]
  simp_rw [Fin.sum_univ_succ, Fin.update_cons_zero, ← Fin.cons_update]
  simp_rw [finiteMean_add]
  rw [finiteMean_const (weight 0) normalized]
  exact add_comm _ _

theorem coordinateVarianceEnergy_eq_sum (count : ℕ)
    (weight : Fin count → Outcome → ℝ)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    coordinateVarianceEnergy count weight response = sumCoordinateVariances weight response := by
  induction count with
  | zero => simp [coordinateVarianceEnergy, sumCoordinateVariances, finiteMean]
  | succ count inductionHypothesis =>
      rw [sumCoordinateVariances_cons weight (normalized 0)]
      simp only [coordinateVarianceEnergy]
      congr 1
      apply congrArg (finiteMean (weight 0))
      funext first
      exact inductionHypothesis (fun coordinate => weight coordinate.succ)
        (fun coordinate => normalized coordinate.succ) (fun rest => response (Fin.cons first rest))

theorem finite_product_variance_le_sum_coordinate_variances (count : ℕ)
    (weight : Fin count → Outcome → ℝ)
    (nonnegative : ∀ coordinate outcome, 0 ≤ weight coordinate outcome)
    (normalized : ∀ coordinate, ∑ outcome, weight coordinate outcome = 1)
    (response : (Fin count → Outcome) → ℝ) :
    finiteVariance (tupleWeight weight) response ≤ sumCoordinateVariances weight response :=
  (finite_product_variance_le_coordinate_energy count weight nonnegative normalized response).trans_eq
    (coordinateVarianceEnergy_eq_sum count weight normalized response)

end IGSIII34.Probability
