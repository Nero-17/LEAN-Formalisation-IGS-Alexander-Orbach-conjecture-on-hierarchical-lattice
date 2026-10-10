import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Probability
noncomputable section

variable {Edge State : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype State]

def productWeight (weight : State → ℝ) (configuration : Edge → State) : ℝ :=
  ∏ edge, weight (configuration edge)

def expectation (weight : State → ℝ) (response : (Edge → State) → ℝ) : ℝ :=
  ∑ configuration, productWeight weight configuration * response configuration

def insertCoordinate (changed : Edge) (value : State)
    (rest : {edge : Edge // edge ≠ changed} → State) : Edge → State :=
  fun edge => if different : edge = changed then value else rest ⟨edge, different⟩

def splitConfiguration (changed : Edge) :
    (Edge → State) ≃ State × ({edge : Edge // edge ≠ changed} → State) where
  toFun configuration := (configuration changed, fun edge => configuration edge.val)
  invFun pair := insertCoordinate changed pair.1 pair.2
  left_inv configuration := by
    funext edge
    simp only [insertCoordinate]
    split <;> simp_all
  right_inv pair := by
    apply Prod.ext
    · simp [insertCoordinate]
    · funext edge
      simp [insertCoordinate, edge.property]

theorem sum_splitConfiguration (changed : Edge) (response : (Edge → State) → ℝ) :
    ∑ configuration, response configuration =
      ∑ rest : {edge : Edge // edge ≠ changed} → State,
        ∑ value : State, response (insertCoordinate changed value rest) := by
  classical
  rw [← (splitConfiguration changed).symm.sum_comp response]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

def erasedWeight (weight : State → ℝ) (configuration : Edge → State) (changed : Edge) : ℝ :=
  ∏ edge ∈ Finset.univ.erase changed, weight (configuration edge)

theorem productWeight_insertCoordinate (weight : State → ℝ) (changed : Edge)
    (base value : State) (rest : {edge : Edge // edge ≠ changed} → State) :
    productWeight weight (insertCoordinate changed value rest) =
      erasedWeight weight (insertCoordinate changed base rest) changed * weight value := by
  unfold productWeight
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ changed)]
  have self : insertCoordinate changed value rest changed = value := by simp [insertCoordinate]
  rw [self]
  congr 1
  apply Finset.prod_congr rfl
  intro edge membership
  simp only [insertCoordinate, Finset.ne_of_mem_erase membership, ↓reduceDIte]

theorem expectation_coordinate_factorisation (weight : State → ℝ)
    (weightSum : ∑ value, weight value = 1) (changed : Edge) (base : State)
    (localResponse : State → ℝ) (otherResponse : (Edge → State) → ℝ)
    (invariant : ∀ configuration value,
      otherResponse (Function.update configuration changed value) = otherResponse configuration) :
    expectation weight (fun configuration => localResponse (configuration changed) * otherResponse configuration) =
      (∑ value, weight value * localResponse value) * expectation weight otherResponse := by
  have responseIndependent (value : State) (rest : {edge : Edge // edge ≠ changed} → State) :
      otherResponse (insertCoordinate changed value rest) =
        otherResponse (insertCoordinate changed base rest) := by
    have updateIdentity : Function.update (insertCoordinate changed base rest) changed value =
        insertCoordinate changed value rest := by
      funext edge
      by_cases same : edge = changed
      · subst edge
        simp [insertCoordinate]
      · simp [insertCoordinate, same]
    rw [← updateIdentity]
    exact invariant _ value
  unfold expectation
  rw [sum_splitConfiguration changed, sum_splitConfiguration changed]
  simp only [productWeight_insertCoordinate weight changed base,
    insertCoordinate, ↓reduceDIte, responseIndependent]
  have factor (rest : {edge : Edge // edge ≠ changed} → State) :
      (∑ value, erasedWeight weight (insertCoordinate changed base rest) changed * weight value *
        (localResponse value * otherResponse (insertCoordinate changed base rest))) =
      (∑ value, weight value * localResponse value) *
        (erasedWeight weight (insertCoordinate changed base rest) changed *
          otherResponse (insertCoordinate changed base rest)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro value _
    ring
  simp_rw [factor]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro rest _
  rw [← Finset.sum_mul, ← Finset.mul_sum, weightSum, mul_one]

theorem productWeight_nonnegative (weight : State → ℝ) (nonnegative : ∀ value, 0 ≤ weight value)
    (configuration : Edge → State) : 0 ≤ productWeight weight configuration :=
  Finset.prod_nonneg (fun edge _ => nonnegative (configuration edge))

theorem sum_productWeight (weight : State → ℝ) (weightSum : ∑ value, weight value = 1) :
    ∑ configuration : Edge → State, productWeight weight configuration = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum (fun (_ : Edge) (value : State) => weight value)]
  simp only [weightSum, Finset.prod_const_one]

theorem expectation_mono (weight : State → ℝ) (nonnegative : ∀ value, 0 ≤ weight value)
    {first second : (Edge → State) → ℝ} (comparison : ∀ configuration, first configuration ≤ second configuration) :
    expectation weight first ≤ expectation weight second := by
  unfold expectation
  exact Finset.sum_le_sum (fun configuration _ =>
    mul_le_mul_of_nonneg_left (comparison configuration) (productWeight_nonnegative weight nonnegative configuration))

theorem expectation_nonnegative (weight : State → ℝ) (nonnegative : ∀ value, 0 ≤ weight value)
    {response : (Edge → State) → ℝ} (responseNonnegative : ∀ configuration, 0 ≤ response configuration) :
    0 ≤ expectation weight response :=
  Finset.sum_nonneg (fun configuration _ =>
    mul_nonneg (productWeight_nonnegative weight nonnegative configuration) (responseNonnegative configuration))

theorem expectation_sum {Index : Type*} [Fintype Index]
    (weight : State → ℝ) (response : Index → (Edge → State) → ℝ) :
    expectation weight (fun configuration => ∑ index, response index configuration) =
      ∑ index, expectation weight (response index) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_const_mul (weight : State → ℝ) (scalar : ℝ) (response : (Edge → State) → ℝ) :
    expectation weight (fun configuration => scalar * response configuration) =
      scalar * expectation weight response := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro configuration _
  ring

end
end IGSIII34.Probability
