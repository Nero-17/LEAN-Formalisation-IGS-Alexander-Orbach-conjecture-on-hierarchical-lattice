import IGSIII34.Percolation.SmallConfiguration
import IGSIII34.Probability.FiniteProduct
import Universality.Percolation.Russo

set_option autoImplicit false

namespace IGSIII34.Probability
noncomputable section

theorem product_mapping_fiber {Index State Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype State] [Fintype Value] [DecidableEq Value]
    (weight : State → ℝ) (mapValue : State → Value) (configuration : Index → Value) :
    (∑ input : Index → State, if (fun index => mapValue (input index)) = configuration then
      (∏ index, weight (input index)) else 0) =
      ∏ index, ∑ state, if mapValue state = configuration index then weight state else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases same : (fun index => mapValue (input index)) = configuration
  · subst configuration
    simp
  · rw [if_neg same]
    symm
    have different : ∃ index, mapValue (input index) ≠ configuration index := by
      by_contra allSame
      exact same (funext fun index => not_not.mp (fun unequal => allSame ⟨index, unequal⟩))
    obtain ⟨index, unequal⟩ := different
    exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg unequal)

theorem product_mapping_observable {Index State Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype State] [Fintype Value] [DecidableEq Value]
    (weight : State → ℝ) (mapValue : State → Value) (response : (Index → Value) → ℝ) :
    (∑ input : Index → State, (∏ index, weight (input index)) *
      response (fun index => mapValue (input index))) =
    ∑ configuration : Index → Value,
      (∏ index, ∑ state, if mapValue state = configuration index then weight state else 0) *
        response configuration := by
  classical
  have expansion (input : Index → State) :
      (∏ index, weight (input index)) * response (fun index => mapValue (input index)) =
      ∑ configuration : Index → Value,
        (if (fun index => mapValue (input index)) = configuration then
          (∏ index, weight (input index)) else 0) * response configuration := by
    simp [ite_mul]
  simp_rw [expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [← Finset.sum_mul, product_mapping_fiber]

end
end IGSIII34.Probability

namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork

def bernoulliPairWeight (parameter retention : ℝ) (bits : Bool × Bool) : ℝ :=
  (if bits.1 then parameter else 1 - parameter) *
    (if bits.2 then retention else 1 - retention)

theorem bernoulliPairWeight_and (parameter retention : ℝ) (opened : Bool) :
    (∑ bits : Bool × Bool, if (bits.1 && bits.2) = opened then
      bernoulliPairWeight parameter retention bits else 0) =
    if opened then parameter * retention else 1 - parameter * retention := by
  cases opened <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliPairWeight] <;> ring

theorem bernoulli_thinning_reliability {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (parameter retention : ℝ) :
    (∑ bits : Fin edges → Bool × Bool,
      (∏ edge, bernoulliPairWeight parameter retention (bits edge)) *
        (if rule.crosses (fun edge => (bits edge).1 && (bits edge).2) then 1 else 0)) =
    rule.reliability (parameter * retention) := by
  have identity := Probability.product_mapping_observable
    (Index := Fin edges) (bernoulliPairWeight parameter retention)
    (fun bits : Bool × Bool => bits.1 && bits.2)
    (fun configuration => if rule.crosses configuration then 1 else 0)
  simpa only [bernoulliPairWeight_and, bernoulliWeight, reliability, mul_ite, mul_one, mul_zero]
    using identity

theorem conditioned_bernoulli_thinning {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (parameter retention : ℝ) :
    (∑ bits : Fin edges → Bool × Bool,
      ((if rule.crosses (fun edge => (bits edge).1) then
        (∏ edge, bernoulliPairWeight parameter retention (bits edge)) else 0) /
        rule.reliability parameter) *
        (if rule.crosses (fun edge => (bits edge).1 && (bits edge).2) then 1 else 0)) =
      rule.reliability (parameter * retention) / rule.reliability parameter := by
  have conditionalEquality (bits : Fin edges → Bool × Bool) :
      ((if rule.crosses (fun edge => (bits edge).1) then
        (∏ edge, bernoulliPairWeight parameter retention (bits edge)) else 0) /
        rule.reliability parameter) *
        (if rule.crosses (fun edge => (bits edge).1 && (bits edge).2) then 1 else 0) =
      ((∏ edge, bernoulliPairWeight parameter retention (bits edge)) *
        (if rule.crosses (fun edge => (bits edge).1 && (bits edge).2) then 1 else 0)) /
          rule.reliability parameter := by
    by_cases thinnedCrosses : rule.crosses (fun edge => (bits edge).1 && (bits edge).2) = true
    · have originalCrosses := rule.crosses_mono _ _
        (fun edge opened => (show (bits edge).1 = true ∧ (bits edge).2 = true from
          by simpa only [Bool.and_eq_true] using opened).1) thinnedCrosses
      simp only [originalCrosses, thinnedCrosses, Bool.true_eq, ↓reduceIte, mul_one]
    · simp only [thinnedCrosses, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_div]
  simp_rw [conditionalEquality, div_eq_mul_inv]
  rw [← Finset.sum_mul, bernoulli_thinning_reliability]

end
end IGSIII34.Percolation
