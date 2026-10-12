import Universality.Percolation.EdgeResampling
import Mathlib.Tactic.Linarith

/-! One-coordinate positive association for the actual finite Bernoulli law.
This proves the first-edge lower bound used for full retained cluster mass
without an assumed FKG certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open Universality.FiniteNetwork
attribute [local instance] Classical.propDecidable

theorem bernoulli_open_response_positive_association
    {edges : ℕ} (response : Configuration edges → ℝ)
    (probability : ℝ) (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (edge : Fin edges)
    (increasing : ∀ rest : RemainingConfiguration edge,
      response (insertEdge edge false rest) ≤ response (insertEdge edge true rest)) :
    probability * expectation probability response ≤
      expectation probability (fun configuration => if configuration edge then response configuration else 0) := by
  classical
  unfold expectation
  rw [sum_splitConfiguration edge, sum_splitConfiguration edge, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rest _
  have weightNonnegative : 0 ≤ erasedWeight probability (insertEdge edge false rest) edge := by
    unfold erasedWeight
    apply Finset.prod_nonneg
    intro other _
    split <;> linarith
  have correctionNonnegative : 0 ≤
      erasedWeight probability (insertEdge edge false rest) edge * probability * (1 - probability) *
        (response (insertEdge edge true rest) - response (insertEdge edge false rest)) :=
    mul_nonneg (mul_nonneg (mul_nonneg weightNonnegative nonnegative) (sub_nonneg.mpr atMostOne))
      (sub_nonneg.mpr (increasing rest))
  simp only [bernoulliWeight_insertEdge, insertEdge_self, Bool.false_eq_true,
    ↓reduceIte, mul_zero, zero_add]
  nlinarith

theorem bernoulli_open_event_positive_association
    {edges : ℕ} (event : Configuration edges → Prop)
    (probability : ℝ) (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (edge : Fin edges)
    (increasing : ∀ rest : RemainingConfiguration edge,
      event (insertEdge edge false rest) → event (insertEdge edge true rest)) :
    probability * expectation probability (fun configuration => if event configuration then 1 else 0) ≤
      expectation probability (fun configuration =>
        if configuration edge = true ∧ event configuration then 1 else 0) := by
  have responseIncreasing (rest : RemainingConfiguration edge) :
      (if event (insertEdge edge false rest) then (1 : ℝ) else 0) ≤
      (if event (insertEdge edge true rest) then (1 : ℝ) else 0) := by
    by_cases first : event (insertEdge edge false rest)
    · simp [first, increasing rest first]
    · by_cases second : event (insertEdge edge true rest) <;> simp [first, second]
  convert bernoulli_open_response_positive_association
    (fun configuration => if event configuration then 1 else 0)
    probability nonnegative atMostOne edge responseIncreasing using 1
  congr 1
  funext configuration
  by_cases opened : configuration edge = true <;> simp [opened]

end
end IGSIII4.SpectralDensity
