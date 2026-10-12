import IGSIII4.SpectralDensity.ActualMomentChernoff

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability
variable {Coordinate Outcome : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Outcome] [Nonempty Outcome]

theorem finiteMean_coordinate (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) (coordinate : Coordinate)
    (response : Outcome → ℝ) :
    finiteMean (productWeight (Edge := Coordinate) weight)
      (fun input => response (input coordinate)) = finiteMean weight response := by
  have factor := expectation_coordinate_factorisation weight normalized coordinate
    (Classical.choice (inferInstance : Nonempty Outcome)) response (fun _ => 1) (fun _ _ => rfl)
  have constant : expectation (Edge := Coordinate) weight (fun _ => 1) = 1 := by
    simp only [expectation, mul_one, sum_productWeight weight normalized]
  rw [constant, mul_one] at factor
  simpa only [mul_one, expectation, finiteMean] using factor

theorem finiteMean_distinct_coordinates (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) (first second : Coordinate)
    (different : first ≠ second) (response : Outcome → ℝ) :
    finiteMean (productWeight (Edge := Coordinate) weight)
      (fun input => response (input first) * response (input second)) =
        finiteMean weight response * finiteMean weight response := by
  have factor := expectation_coordinate_factorisation weight normalized first
    (Classical.choice (inferInstance : Nonempty Outcome)) response
    (fun input => response (input second)) (by
      intro input value
      simp only [Function.update_of_ne different.symm])
  change _ = finiteMean weight response *
    finiteMean (productWeight (Edge := Coordinate) weight) (fun input => response (input second)) at factor
  rw [finiteMean_coordinate weight normalized second response] at factor
  exact factor

/-- Exact diagonal/off-diagonal expansion of an independent path's second moment. -/
theorem finiteMean_path_second_moment (weight response : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1)
    (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean (productWeight (Edge := Coordinate) weight)
      (fun input => (∑ coordinate, response (input coordinate)) ^ 2) ≤
        (Fintype.card Coordinate : ℝ) ^ 2 + 8 * Fintype.card Coordinate := by
  classical
  have secondMoment : finiteMean weight (fun outcome => response outcome ^ 2) ≤ 9 := by
    rw [finiteVariance_eq_second_moment weight response normalized, meanOne] at varianceBound
    linarith
  have expansion (input : Coordinate → Outcome) :
      (∑ coordinate, response (input coordinate)) ^ 2 =
        ∑ first, ∑ second, response (input first) * response (input second) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
  have average : finiteMean (productWeight (Edge := Coordinate) weight)
      (fun input => (∑ coordinate, response (input coordinate)) ^ 2) =
        ∑ first : Coordinate, ∑ second : Coordinate,
          finiteMean (productWeight (Edge := Coordinate) weight)
            (fun input => response (input first) * response (input second)) := by
    simp only [finiteMean, expansion, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_comm]
  have pairMean (first second : Coordinate) :
      finiteMean (productWeight (Edge := Coordinate) weight)
        (fun input => response (input first) * response (input second)) =
          if second = first then finiteMean weight (fun outcome => response outcome ^ 2) else 1 := by
    by_cases same : second = first
    · subst second
      simp only [↓reduceIte]
      convert finiteMean_coordinate weight normalized first
        (fun outcome => response outcome ^ 2) using 1 <;> first | rfl | (simp only [pow_two])
    · rw [finiteMean_distinct_coordinates weight normalized first second (Ne.symm same), meanOne]
      simp [same]
  rw [average]
  simp only [pairMean]
  have row (first : Coordinate) :
      (∑ second : Coordinate, if second = first then finiteMean weight (fun outcome => response outcome ^ 2) else (1 : ℝ)) =
        finiteMean weight (fun outcome => response outcome ^ 2) + (Fintype.card Coordinate : ℝ) - 1 := by
    have pointwise (second : Coordinate) :
        (if second = first then finiteMean weight (fun outcome => response outcome ^ 2) else (1 : ℝ)) =
          (if second = first then finiteMean weight (fun outcome => response outcome ^ 2) - 1 else 0) + 1 := by
      split_ifs <;> ring
    simp only [pointwise, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  simp only [row, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have countNonnegative : (0 : ℝ) ≤ Fintype.card Coordinate := Nat.cast_nonneg _
  nlinarith

end
end IGSIII4.SpectralDensity
