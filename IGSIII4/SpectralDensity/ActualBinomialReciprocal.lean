import IGSIII4.SpectralDensity.ActualSuccessCount
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

def permutationConfiguration (paths : ℕ) (permutation : Equiv.Perm (Fin paths)) :
    Configuration paths ≃ Configuration paths where
  toFun configuration := fun path => configuration (permutation path)
  invFun configuration := fun path => configuration (permutation.symm path)
  left_inv configuration := by funext path; simp
  right_inv configuration := by funext path; simp

theorem permutation_weight (paths : ℕ) (permutation : Equiv.Perm (Fin paths))
    (probability : ℝ) (configuration : Configuration paths) :
    bernoulliWeight probability (permutationConfiguration paths permutation configuration) =
      bernoulliWeight probability configuration := by
  exact Equiv.prod_comp permutation (fun path => if configuration path then probability else 1 - probability)

theorem permutation_successCount (paths : ℕ) (permutation : Equiv.Perm (Fin paths))
    (configuration : Configuration paths) :
    successCount paths (permutationConfiguration paths permutation configuration) =
      successCount paths configuration := by
  exact Equiv.sum_comp permutation (fun path => if configuration path then (1 : ℕ) else 0)

theorem expectation_permutation (paths : ℕ) (permutation : Equiv.Perm (Fin paths))
    (probability : ℝ) (response : Configuration paths → ℝ) :
    expectation probability (fun configuration => response (permutationConfiguration paths permutation configuration)) =
      expectation probability response := by
  unfold expectation
  have identity := (permutationConfiguration paths permutation).sum_comp
    (fun configuration => bernoulliWeight probability configuration * response configuration)
  simpa only [permutation_weight] using identity

theorem successCount_zero_probability (paths : ℕ) (probability : ℝ) :
    expectation probability (fun configuration => if successCount paths configuration = 0 then 1 else 0) =
      (1 - probability) ^ paths := by
  induction paths with
  | zero => simp [successCount, expectation_const]
  | succ paths inductionHypothesis =>
    rw [expectation_cons]
    simp only [successCount_cons]
    simp only [Bool.false_eq_true, if_false, if_true, zero_add, Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and]
    rw [expectation_const, inductionHypothesis, pow_succ]
    ring

theorem successCount_positive_probability (paths : ℕ) (probability : ℝ) :
    expectation probability (fun configuration => if 0 < successCount paths configuration then 1 else 0) =
      1 - (1 - probability) ^ paths := by
  have complement := finite_event_complement (bernoulliWeight probability)
    (sum_bernoulliWeight probability) (fun configuration => successCount paths configuration = 0)
  have rewriteEvent (configuration : Configuration paths) :
      ¬ successCount paths configuration = 0 ↔ 0 < successCount paths configuration := by omega
  simp_rw [rewriteEvent] at complement
  have zeroProbability := successCount_zero_probability paths probability
  simp only [expectation, mul_ite, mul_one, mul_zero] at zeroProbability ⊢
  have zeroProbabilityClassical : (∑ configuration : Configuration paths,
      @ite ℝ (successCount paths configuration = 0) (Classical.propDecidable _)
        (bernoulliWeight probability configuration) 0) = (1 - probability) ^ paths := by
    convert zeroProbability using 1
    apply Finset.sum_congr rfl
    intro configuration _
    by_cases zero : successCount paths configuration = 0 <;> simp [zero]
  exact complement.trans (congrArg (fun value : ℝ => 1 - value) zeroProbabilityClassical)

theorem reciprocal_coordinate_symmetry (paths : ℕ) (probability : ℝ) (path : Fin (paths + 1)) :
    expectation probability (fun configuration : Configuration (paths + 1) =>
      if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0) =
    expectation probability (fun configuration : Configuration (paths + 1) =>
      if configuration 0 then 1 / (successCount (paths + 1) configuration : ℝ) else 0) := by
  have identity := expectation_permutation (paths + 1) (Equiv.swap path 0) probability
    (fun configuration => if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0)
  have responseIdentity :
      (fun configuration : Configuration (paths + 1) =>
        if (permutationConfiguration (paths + 1) (Equiv.swap path 0) configuration) path then
          1 / (successCount (paths + 1) (permutationConfiguration (paths + 1) (Equiv.swap path 0) configuration) : ℝ) else 0) =
      (fun configuration => if configuration 0 then 1 / (successCount (paths + 1) configuration : ℝ) else 0) := by
    funext configuration
    rw [permutation_successCount]
    simp only [permutationConfiguration, Equiv.coe_fn_mk, Equiv.swap_apply_left]
  rw [responseIdentity] at identity
  exact identity.symm

theorem binomial_shifted_reciprocal_identity (paths : ℕ) (probability : ℝ) :
    ((paths + 1 : ℕ) : ℝ) * probability *
      expectation probability (fun configuration : Configuration paths =>
        1 / ((successCount paths configuration : ℝ) + 1)) =
      1 - (1 - probability) ^ (paths + 1) := by
  have indicatorSum (configuration : Configuration (paths + 1)) :
      (∑ path, if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0) =
        if 0 < successCount (paths + 1) configuration then 1 else 0 := by
    have identity : (∑ path, if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0) =
        (successCount (paths + 1) configuration : ℝ) / (successCount (paths + 1) configuration : ℝ) := by
      rw [successCount, Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro path _
      cases equal : configuration path <;> simp [equal]
    rw [identity]
    by_cases positive : 0 < successCount (paths + 1) configuration
    · simp [positive, Nat.cast_ne_zero.mpr (by omega : successCount (paths + 1) configuration ≠ 0)]
    · have zero : successCount (paths + 1) configuration = 0 := by omega
      simp [zero]
  have sumIdentity : expectation probability (fun configuration : Configuration (paths + 1) =>
        ∑ path, if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0) =
      ∑ path : Fin (paths + 1), expectation probability (fun configuration : Configuration (paths + 1) =>
        if configuration path then 1 / (successCount (paths + 1) configuration : ℝ) else 0) := by
    unfold expectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [reciprocal_coordinate_symmetry paths probability] at sumIdentity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at sumIdentity
  have headIdentity : expectation probability (fun configuration : Configuration (paths + 1) =>
      if configuration 0 then 1 / (successCount (paths + 1) configuration : ℝ) else 0) =
        probability * expectation probability (fun configuration : Configuration paths =>
          1 / ((successCount paths configuration : ℝ) + 1)) := by
    rw [expectation_cons]
    simp only [Fin.cons_zero, Bool.false_eq_true, if_false, if_true, successCount_cons,
      Nat.cast_add, Nat.cast_one]
    rw [expectation_const]
    simp only [mul_zero, zero_add, add_comm]
  rw [headIdentity] at sumIdentity
  simp_rw [indicatorSum] at sumIdentity
  rw [successCount_positive_probability] at sumIdentity
  linarith [sumIdentity]

theorem binomial_shifted_reciprocal_bound (paths : ℕ) (probability : ℝ)
    (positive : 0 < probability) (atMostOne : probability ≤ 1) :
    expectation probability (fun configuration : Configuration paths =>
      1 / ((successCount paths configuration : ℝ) + 1)) ≤ 1 / (((paths : ℝ) + 1) * probability) := by
  have identity := binomial_shifted_reciprocal_identity paths probability
  have powerNonnegative : 0 ≤ (1 - probability) ^ (paths + 1) := by positivity
  apply (le_div_iff₀ (by positivity : 0 < ((paths : ℝ) + 1) * probability)).mpr
  push_cast at identity
  nlinarith

theorem binomial_reciprocal_conditional_bound (paths : ℕ) (pathsPositive : 0 < paths)
    (probability : ℝ) (positive : 0 < probability) (atMostOne : probability ≤ 1)
    (crossingLarge : 1 / 2 < 1 - (1 - probability) ^ paths) :
    expectation probability (fun configuration : Configuration paths =>
      if 0 < successCount paths configuration then 1 / (successCount paths configuration : ℝ) else 0) /
        (1 - (1 - probability) ^ paths) ≤ 4 / ((paths : ℝ) * probability) := by
  have pointwise (configuration : Configuration paths) :
      (if 0 < successCount paths configuration then 1 / (successCount paths configuration : ℝ) else 0) ≤
        2 * (1 / ((successCount paths configuration : ℝ) + 1)) := by
    split_ifs with countPositive
    · have countRealPositive : 0 < (successCount paths configuration : ℝ) := by exact_mod_cast countPositive
      have countAtLeastOne : 1 ≤ (successCount paths configuration : ℝ) := by exact_mod_cast countPositive
      apply (div_le_iff₀ countRealPositive).mpr
      field_simp
      nlinarith
    · positivity
  have comparison := Finset.sum_le_sum (fun configuration (_ : configuration ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pointwise configuration) (bernoulliWeight_nonneg positive.le atMostOne configuration))
  change expectation probability _ ≤ expectation probability (fun configuration =>
    2 * (1 / ((successCount paths configuration : ℝ) + 1))) at comparison
  rw [expectation_const_mul] at comparison
  have inverseBound := binomial_shifted_reciprocal_bound paths probability positive atMostOne
  have pathsRealPositive : 0 < (paths : ℝ) := by exact_mod_cast pathsPositive
  have crossingPositive : 0 < 1 - (1 - probability) ^ paths := by linarith
  apply (div_le_iff₀ crossingPositive).mpr
  have denominatorPositive : 0 < ((paths : ℝ) + 1) * probability := by positivity
  have productPositive : 0 < (paths : ℝ) * probability := by positivity
  have scaled := mul_le_mul_of_nonneg_left inverseBound (by norm_num : (0 : ℝ) ≤ 2)
  have denominatorCompare : 1 / (((paths : ℝ) + 1) * probability) ≤ 1 / ((paths : ℝ) * probability) := by
    apply one_div_le_one_div_of_le productPositive
    nlinarith
  have finalBound : 2 / ((paths : ℝ) * probability) ≤
      4 / ((paths : ℝ) * probability) * (1 - (1 - probability) ^ paths) := by
    apply (div_le_iff₀ productPositive).mpr
    field_simp
    nlinarith
  calc
    _ ≤ 2 * (1 / (((paths : ℝ) + 1) * probability)) := comparison.trans scaled
    _ ≤ 2 * (1 / ((paths : ℝ) * probability)) := mul_le_mul_of_nonneg_left denominatorCompare (by norm_num)
    _ = 2 / ((paths : ℝ) * probability) := by ring
    _ ≤ _ := finalBound

end
end IGSIII4.SpectralDensity.ActualFamily
