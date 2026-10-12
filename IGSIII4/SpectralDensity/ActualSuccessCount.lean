import IGSIII4.SpectralDensity.BernoulliCircuit
import IGSIII34.Probability.FiniteProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem finite_product_pushforward {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output] [DecidableEq Output]
    (weight : Input → ℝ) (map : Input → Output) (response : (Index → Output) → ℝ) :
    (∑ configuration : Index → Input,
      (∏ index, weight (configuration index)) * response (fun index => map (configuration index))) =
    ∑ output : Index → Output,
      (∏ index, ∑ input : Input, if map input = output index then weight input else 0) * response output := by
  have productFiber (configuration : Index → Input) (output : Index → Output) :
      (∏ index, if map (configuration index) = output index then weight (configuration index) else 0) =
        if (fun index => map (configuration index)) = output then ∏ index, weight (configuration index) else 0 := by
    rw [Fintype.prod_ite_zero]
    simp only [funext_iff]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  simp_rw [productFiber, ite_mul, zero_mul]
  simp

def successCount (paths : ℕ) (configuration : Configuration paths) : ℕ :=
  ∑ path, if configuration path then 1 else 0

def pathStatuses (paths length : ℕ) (configuration : Fin paths → Configuration length) : Configuration paths :=
  fun path => decide (pathCrossing length (configuration path))

theorem path_status_weight (length : ℕ) (probability : ℝ) (status : Bool) :
    (∑ configuration : Configuration length,
      if decide (pathCrossing length configuration) = status then bernoulliWeight probability configuration else 0) =
        if status then probability ^ length else 1 - probability ^ length := by
  cases status
  · simp only [Bool.false_eq_true, if_false]
    have identity := finite_event_complement (bernoulliWeight probability)
      (sum_bernoulliWeight probability) (pathCrossing length)
    rw [path_crossing_probability] at identity
    convert identity using 1
    apply Finset.sum_congr rfl
    intro configuration _
    by_cases crossing : pathCrossing length configuration <;> simp [crossing]
  · simp only [if_true]
    convert path_crossing_probability length probability using 1
    apply Finset.sum_congr rfl
    intro configuration _
    by_cases crossing : pathCrossing length configuration <;> simp [crossing]

/-- The entire actual independent path-status vector has the finite Bernoulli law. -/
theorem path_status_law (paths length : ℕ) (probability : ℝ) (response : Configuration paths → ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      blockWeight paths length probability configuration * response (pathStatuses paths length configuration)) =
        expectation (probability ^ length) response := by
  unfold blockWeight pathStatuses
  rw [finite_product_pushforward (bernoulliWeight probability) (fun configuration => decide (pathCrossing length configuration)) response]
  simp_rw [path_status_weight]
  rfl

theorem successCount_cons (paths : ℕ) (opened : Bool) (configuration : Configuration paths) :
    successCount (paths + 1) (Fin.cons opened configuration) =
      (if opened then 1 else 0) + successCount paths configuration := by
  simp only [successCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem successCount_zero : ∀ configuration : Configuration 0, successCount 0 configuration = 0 := by
  intro configuration
  simp [successCount]

theorem successCount_positive_iff (paths : ℕ) (configuration : Configuration paths) :
    0 < successCount paths configuration ↔ ∃ path, configuration path = true := by
  simp only [successCount, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _), Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨path, opened⟩
    refine ⟨path, ?_⟩
    cases equal : configuration path <;> simp [equal] at opened ⊢
  · rintro ⟨path, opened⟩
    exact ⟨path, by simp [opened]⟩

theorem successCount_mean (paths : ℕ) (probability : ℝ) :
    expectation probability (fun configuration => (successCount paths configuration : ℝ)) =
      (paths : ℝ) * probability := by
  induction paths with
  | zero => simp [successCount, expectation_const]
  | succ paths inductionHypothesis =>
    rw [expectation_cons]
    simp only [successCount_cons, Bool.false_eq_true, if_false, if_true,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    rw [expectation_add, expectation_const, inductionHypothesis]
    push_cast
    ring

theorem actual_path_successCount_mean (paths length : ℕ) (probability : ℝ) :
    (∑ configuration : Fin paths → Configuration length,
      blockWeight paths length probability configuration *
        (successCount paths (pathStatuses paths length configuration) : ℝ)) =
      (paths : ℝ) * probability ^ length := by
  rw [path_status_law paths length probability (fun configuration => (successCount paths configuration : ℝ)), successCount_mean]

end
end IGSIII4.SpectralDensity.ActualFamily
