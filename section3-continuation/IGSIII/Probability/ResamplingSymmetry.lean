import IGSIII.Probability.FiniteResampling

/-! The old and resampled values of one product coordinate can be exchanged,
including when its probability weight vanishes. No division by a weight occurs. -/

set_option autoImplicit false

namespace IGSIII.Probability

open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome] {count : ℕ}

def resamplingExchange (coordinate : Fin count) :
    ((Fin count → Outcome) × Outcome) ≃ ((Fin count → Outcome) × Outcome) where
  toFun pair := (Function.update pair.1 coordinate pair.2, pair.1 coordinate)
  invFun pair := (Function.update pair.1 coordinate pair.2, pair.1 coordinate)
  left_inv pair := by
    apply Prod.ext
    · funext index
      by_cases equal : index = coordinate <;> simp [equal]
    · simp
  right_inv pair := by
    apply Prod.ext
    · funext index
      by_cases equal : index = coordinate <;> simp [equal]
    · simp

omit [Fintype Outcome] in
theorem tupleWeight_update_exchange (weight : Fin count → Outcome → ℝ)
    (coordinate : Fin count) (outcome : Fin count → Outcome) (replacement : Outcome) :
    tupleWeight weight (Function.update outcome coordinate replacement) * weight coordinate (outcome coordinate) =
      tupleWeight weight outcome * weight coordinate replacement := by
  unfold tupleWeight
  rw [← Finset.prod_erase_mul Finset.univ
    (fun index => weight index (Function.update outcome coordinate replacement index)) (Finset.mem_univ coordinate)]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun index => weight index (outcome index)) (Finset.mem_univ coordinate)]
  have remaining :
      (∏ index ∈ Finset.univ.erase coordinate,
        weight index (Function.update outcome coordinate replacement index)) =
      ∏ index ∈ Finset.univ.erase coordinate, weight index (outcome index) := by
    apply Finset.prod_congr rfl
    intro index present
    rw [Function.update_of_ne (Finset.ne_of_mem_erase present)]
  rw [remaining, Function.update_self]
  ring

theorem finiteMean_resampling_exchange (weight : Fin count → Outcome → ℝ)
    (coordinate : Fin count) (response : ((Fin count → Outcome) × Outcome) → ℝ) :
    finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
      tupleWeight weight pair.1 * weight coordinate pair.2) response =
      finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
        tupleWeight weight pair.1 * weight coordinate pair.2)
        (fun pair => response (resamplingExchange coordinate pair)) := by
  calc
    _ = ∑ pair : (Fin count → Outcome) × Outcome,
        (tupleWeight weight (resamplingExchange coordinate pair).1 *
          weight coordinate (resamplingExchange coordinate pair).2) *
            response (resamplingExchange coordinate pair) :=
      ((resamplingExchange coordinate).sum_comp (fun pair =>
        (tupleWeight weight pair.1 * weight coordinate pair.2) * response pair)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pair _
      rw [show (resamplingExchange coordinate pair).1 =
        Function.update pair.1 coordinate pair.2 from rfl]
      rw [show (resamplingExchange coordinate pair).2 = pair.1 coordinate from rfl]
      rw [tupleWeight_update_exchange]

end IGSIII.Probability
