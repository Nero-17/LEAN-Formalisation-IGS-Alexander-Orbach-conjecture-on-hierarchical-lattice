import Universality.Percolation.WheatstoneKernels
import Universality.Percolation.Bernoulli
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

namespace Universality.Section5
noncomputable section
open FiniteNetwork Matrix

/-- Casts of the actual rational opposite-pair and central-slot kernels. -/
def K3real : Matrix LiveState LiveState ℝ := outerPairKernel.map Rat.cast
def J3real : Matrix LiveState LiveState ℝ := centralKernel.map Rat.cast

private theorem slot_response_eq (slots : Finset (Fin 5)) (σ : LiveState)
    (configuration : Configuration 5) (values : LiveState → ℝ) :
    (∑ edge ∈ slots, match wheatstoneNetwork.childState σ configuration edge with
      | some state => values state
      | none => 0) =
    ∑ state : LiveState,
      ((slots.filter fun edge => wheatstoneNetwork.childState σ configuration edge = some state).card : ℝ) *
        values state := by
  symm
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  cases wheatstoneNetwork.childState σ configuration edge <;> simp

private theorem slot_conditional_sum_eq (slots : Finset (Fin 5)) (σ : LiveState)
    (values : LiveState → ℝ) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      ∑ edge ∈ slots, match wheatstoneNetwork.childState σ configuration edge with
        | some state => values state
        | none => 0
      else 0) =
    ∑ state : LiveState, (wheatstoneSlotCount slots σ state : ℝ) * values state := by
  simp only [wheatstoneSlotCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  cases conditioning : wheatstoneNetwork.conditioning σ configuration
  · simp
  · simp only [↓reduceIte]
    exact slot_response_eq slots σ configuration values

theorem wheatstone_slot_conditional_response (slots : Finset (Fin 5))
    (matrix : Matrix LiveState LiveState ℝ) (σ τ : LiveState) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      bernoulliWeight (1 / 2) configuration *
        ∑ edge ∈ slots, match wheatstoneNetwork.childState σ configuration edge with
          | some state => matrix state τ
          | none => 0
      else 0) / wheatstoneNetwork.conditioningProbability (1 / 2) σ =
      ∑ state : LiveState, ((wheatstoneSlotCount slots σ state : ℝ) / 16) * matrix state τ := by
  simp only [bernoulliWeight_half, conditioningProbability_half, wheatstone_exact_counts.1]
  have factor :
      (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
        (1 / 2 : ℝ) ^ 5 *
          ∑ edge ∈ slots, match wheatstoneNetwork.childState σ configuration edge with
            | some state => matrix state τ
            | none => 0
        else 0) =
      (1 / 2 : ℝ) ^ 5 *
        ∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
          ∑ edge ∈ slots, match wheatstoneNetwork.childState σ configuration edge with
            | some state => matrix state τ
            | none => 0
          else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro configuration _
    split <;> simp
  rw [factor, mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ^ 5 ≠ 0),
    slot_conditional_sum_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  ring

theorem wheatstone_outer_pair_conditional_response
    (matrix : Matrix LiveState LiveState ℝ) (σ τ : LiveState) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      bernoulliWeight (1 / 2) configuration *
        ∑ edge ∈ ({0, 3} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
          | some state => matrix state τ
          | none => 0
      else 0) / wheatstoneNetwork.conditioningProbability (1 / 2) σ =
      (K3real * matrix) σ τ := by
  rw [wheatstone_slot_conditional_response]
  simp only [wheatstone_outer_pair_counts.1, Matrix.mul_apply, K3real, Matrix.map_apply,
    outerPairKernel, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]

theorem wheatstone_other_pair_conditional_response
    (matrix : Matrix LiveState LiveState ℝ) (σ τ : LiveState) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      bernoulliWeight (1 / 2) configuration *
        ∑ edge ∈ ({1, 2} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
          | some state => matrix state τ
          | none => 0
      else 0) / wheatstoneNetwork.conditioningProbability (1 / 2) σ =
      (K3real * matrix) σ τ := by
  rw [wheatstone_slot_conditional_response]
  simp only [wheatstone_outer_pair_counts.2, Matrix.mul_apply, K3real, Matrix.map_apply,
    outerPairKernel, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]

theorem wheatstone_central_conditional_response
    (matrix : Matrix LiveState LiveState ℝ) (σ τ : LiveState) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      bernoulliWeight (1 / 2) configuration *
        ∑ edge ∈ ({4} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
          | some state => matrix state τ
          | none => 0
      else 0) / wheatstoneNetwork.conditioningProbability (1 / 2) σ =
      (J3real * matrix) σ τ := by
  rw [wheatstone_slot_conditional_response]
  simp only [wheatstone_central_counts, Matrix.mul_apply, J3real, Matrix.map_apply,
    centralKernel, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]

theorem wheatstone_mass_kernel_aggregation
    (a b c : Matrix LiveState LiveState ℝ) (σ τ : LiveState) :
    (∑ configuration : Configuration 5, if wheatstoneNetwork.conditioning σ configuration then
      bernoulliWeight (1 / 2) configuration *
        ∑ edge : Fin 5, match wheatstoneNetwork.childState σ configuration edge with
          | some state => (![a, b, b, a, c] edge) state τ
          | none => 0
      else 0) / wheatstoneNetwork.conditioningProbability (1 / 2) σ =
      (K3real * a + K3real * b + J3real * c) σ τ := by
  have splitSlots (configuration : Configuration 5) :
      (∑ edge : Fin 5, match wheatstoneNetwork.childState σ configuration edge with
        | some state => (![a, b, b, a, c] edge) state τ
        | none => 0) =
      (∑ edge ∈ ({0, 3} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
        | some state => a state τ | none => 0) +
      (∑ edge ∈ ({1, 2} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
        | some state => b state τ | none => 0) +
      (∑ edge ∈ ({4} : Finset (Fin 5)), match wheatstoneNetwork.childState σ configuration edge with
        | some state => c state τ | none => 0) := by
    simp [Fin.sum_univ_succ]
    ring
  have splitIf (condition : Prop) [Decidable condition] (x y : ℝ) :
      (if condition then x + y else 0) =
        (if condition then x else 0) + (if condition then y else 0) := by
    split <;> simp
  simp only [splitSlots, mul_add, splitIf, Finset.sum_add_distrib, add_div]
  rw [wheatstone_outer_pair_conditional_response, wheatstone_other_pair_conditional_response,
    wheatstone_central_conditional_response]
  rfl

end
end Universality.Section5
