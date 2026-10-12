import IGSIII4.SpectralDensity.ActualMomentConditionalBlock20261012
import IGSIII4.SpectralDensity.ActualBinomialConditional20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable

def conditionalActualBlockWeight (paths length : ℕ) (probability : ℝ)
    (configuration : Fin paths → Configuration length) : ℝ :=
  if blockCrossing paths length configuration then
    blockWeight paths length probability configuration /
      (1 - (1 - probability ^ length) ^ paths) else 0

theorem successfulPathCount_cast20261012 (paths : ℕ) (success : Configuration paths) :
    successfulPathCount success = (successCount paths success : ℝ) := by
  simp only [successfulPathCount, successCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro path _
  cases equal : success path <;> simp [equal]

theorem actual_block_crossing_status20261012 (paths length : ℕ)
    (configuration : Fin paths → Configuration length) :
    blockCrossing paths length configuration ↔
      0 < successCount paths (pathStatuses paths length configuration) := by
  rw [successCount_positive_iff]
  simp only [blockCrossing, pathStatuses, decide_eq_true_eq]

/-- Conditioning the actual independent path configurations is exactly the
conditioned Bernoulli success-status law, for every observable. -/
theorem conditional_actual_block_status_law20261012 (paths length : ℕ) (probability : ℝ)
    (response : Configuration paths → ℝ) :
    finiteMean (conditionalActualBlockWeight paths length probability)
      (fun configuration => response (pathStatuses paths length configuration)) =
      finiteMean (conditionalStatusWeight paths (probability ^ length)) response := by
  rw [conditionalStatusWeight_expectation]
  unfold finiteMean conditionalActualBlockWeight
  have average : (∑ configuration : Fin paths → Configuration length,
      (if blockCrossing paths length configuration then
        blockWeight paths length probability configuration / (1 - (1 - probability ^ length) ^ paths) else 0) *
        response (pathStatuses paths length configuration)) =
      (∑ configuration : Fin paths → Configuration length,
        blockWeight paths length probability configuration *
          (if 0 < successCount paths (pathStatuses paths length configuration) then
            response (pathStatuses paths length configuration) else 0)) /
              (1 - (1 - probability ^ length) ^ paths) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro configuration _
    by_cases crosses : blockCrossing paths length configuration
    · have success := (actual_block_crossing_status20261012 paths length configuration).mp crosses
      simp only [crosses, success, ↓reduceIte]
      ring
    · have failed : ¬0 < successCount paths (pathStatuses paths length configuration) :=
        fun success => crosses ((actual_block_crossing_status20261012 paths length configuration).mpr success)
      simp only [crosses, failed, ↓reduceIte, zero_mul, mul_zero, zero_div]
  rw [average, path_status_law paths length probability
    (fun success => if 0 < successCount paths success then response success else 0)]

def actualBlockObservable {Outcome : Type*} [Fintype Outcome]
    (paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ)
    (observable : ℝ → ℝ) : ℝ :=
  finiteMean (conditionalActualBlockWeight paths length probability) (fun configuration =>
    finiteMean (blockProductWeight weight) (fun input : Fin paths → Fin length → Outcome =>
      observable (blockInputResponse (pathStatuses paths length configuration) response input)))

theorem actualBlockObservable_eq_status20261012 {Outcome : Type*} [Fintype Outcome]
    (paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ) (observable : ℝ → ℝ) :
    actualBlockObservable paths length probability weight response observable =
      conditionalBlockObservable (length := length)
        (conditionalStatusWeight paths (probability ^ length)) weight response observable := by
  unfold actualBlockObservable conditionalBlockObservable
  exact conditional_actual_block_status_law20261012 paths length probability
    (fun success => finiteMean (blockProductWeight weight)
      (fun input : Fin paths → Fin length → Outcome => observable (blockInputResponse success response input)))

theorem actualBlock_second_moment20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    actualBlockObservable paths length probability weight response (fun value => value ^ 2) ≤
      (length : ℝ) ^ 2 + 8 * length := by
  rw [actualBlockObservable_eq_status20261012]
  exact conditionalBlock_second_moment20261012 _
    (conditionalStatusWeight_nonnegative paths _ (pow_nonneg probabilityNonnegative length)
      (pow_le_one₀ probabilityNonnegative probabilityAtMostOne) crossingPositive)
    (conditionalStatusWeight_normalized paths _ crossingPositive)
    (conditionalStatusWeight_zero paths _) weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound

theorem actualBlock_mean_lower20261012 {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (probabilityNonnegative : 0 ≤ probability)
    (probabilityAtMostOne : probability ≤ 1)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (positive : ∀ outcome, 0 < response outcome)
    (lengthPositive : 0 < length) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    (length : ℝ) / 2 * finiteMean (conditionalStatusWeight paths (probability ^ length))
      (fun success => 1 / (successCount paths success : ℝ)) -
        (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length ≤
      actualBlockObservable paths length probability weight response id := by
  rw [actualBlockObservable_eq_status20261012]
  simpa only [successfulPathCount_cast20261012] using conditionalBlock_mean_lower20261012 _
    (conditionalStatusWeight_nonnegative paths _ (pow_nonneg probabilityNonnegative length)
      (pow_le_one₀ probabilityNonnegative probabilityAtMostOne) crossingPositive)
    (conditionalStatusWeight_normalized paths _ crossingPositive)
    (conditionalStatusWeight_zero paths _) weight response weightNonnegative normalized positive lengthPositive meanOne varianceBound

end
end IGSIII4.SpectralDensity.ActualFamily
