import IGSIII.Chemical.SmallBall.FactorialMoments
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Filter
open scoped Topology
open scoped BigOperators

theorem eventually_weak_compositions_le_geometric (length : ℕ) {base : ℝ} (baseGreaterOne : 1 < base) :
    ∃ threshold : ℕ, ∀ power, threshold ≤ power →
      (((length + power - 1).choose power : ℕ) : ℝ) ≤ base ^ power := by
  have basePositive : 0 < base := lt_trans zero_lt_one baseGreaterOne
  by_cases lengthZero : length = 0
  · subst length
    refine ⟨1, fun power powerPositive => ?_⟩
    rw [Nat.zero_add, Nat.choose_eq_zero_of_lt (by omega : power - 1 < power), Nat.cast_zero]
    exact pow_nonneg basePositive.le power
  have lengthPositive : 1 ≤ length := Nat.pos_of_ne_zero lengthZero
  have geometricLimit := (tendsto_pow_const_mul_const_pow_of_lt_one (length - 1)
    (inv_nonneg.mpr basePositive.le)
    ((inv_lt_one₀ basePositive).mpr baseGreaterOne)).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨threshold, thresholdValid⟩ := Filter.eventually_atTop.mp
    (geometricLimit.eventually (gt_mem_nhds (inv_pos.mpr basePositive)))
  refine ⟨threshold, fun power powerLarge => ?_⟩
  have comparison := thresholdValid power powerLarge
  simp only [Function.comp_apply, pow_succ] at comparison
  have canceled : (((power + 1 : ℕ) : ℝ) ^ (length - 1)) * (base⁻¹) ^ power < 1 := by
    nlinarith [inv_pos.mpr basePositive]
  have polynomialBound : (((power + 1 : ℕ) : ℝ) ^ (length - 1)) < base ^ power :=
    (div_lt_one (pow_pos basePositive power)).mp
      (by simpa only [div_eq_mul_inv, inv_pow] using canceled)
  have compositionBound : (length + power - 1).choose power ≤ (power + 1) ^ (length - 1) := by
    have topIdentity : length + power - 1 = power + (length - 1) := by omega
    rw [topIdentity, Nat.choose_symm_add]
    exact Nat.choose_add_le_add_one_pow power (length - 1)
  exact (by exact_mod_cast compositionBound :
    (((length + power - 1).choose power : ℕ) : ℝ) ≤
      ((power + 1 : ℕ) : ℝ) ^ (length - 1)).trans polynomialBound.le

theorem exists_finite_factorial_bound {Outcome : Type*} [Fintype Outcome]
    (weight value : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (valueNonnegative : ∀ outcome, 0 ≤ value outcome) (normalized : ∑ outcome, weight outcome = 1) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ power : ℕ,
      (∑ outcome, weight outcome * value outcome ^ power) ≤ constant ^ power * (power.factorial : ℝ) := by
  classical
  refine ⟨max 1 (∑ outcome, value outcome), le_max_left _ _, fun power => ?_⟩
  have constantNonnegative : 0 ≤ max 1 (∑ outcome, value outcome) :=
    zero_le_one.trans (le_max_left _ _)
  calc
    _ ≤ ∑ outcome, weight outcome * max 1 (∑ other, value other) ^ power := Finset.sum_le_sum
      (fun outcome _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (valueNonnegative outcome)
          ((Finset.single_le_sum (fun other _ => valueNonnegative other) (Finset.mem_univ outcome)).trans
            (le_max_right _ _)) power) (weightNonnegative outcome))
    _ = max 1 (∑ outcome, value outcome) ^ power := by rw [← Finset.sum_mul, normalized, one_mul]
    _ ≤ _ := le_mul_of_one_le_right (pow_nonneg constantNonnegative power)
      (by exact_mod_cast Nat.factorial_pos power)

theorem exists_uniform_factorial_majorant {moment : ℕ → ℕ → ℝ}
    (zeroOrder : ∀ depth, moment depth 0 = 1)
    (naturalBounds : ∀ power, ∃ bound : ℝ, ∀ depth, moment depth power ≤ bound)
    (initialBound : ∃ constant : ℝ, 1 ≤ constant ∧ ∀ power,
      moment 0 power ≤ constant ^ power * (power.factorial : ℝ))
    (eventualPreservation : ∃ threshold : ℕ, ∀ power, threshold ≤ power → ∀ depth,
      ∀ constant : ℝ, 1 ≤ constant →
      (∀ order, order ≤ power → moment depth order ≤ constant ^ order * (order.factorial : ℝ)) →
        moment (depth + 1) power ≤ constant ^ power * (power.factorial : ℝ)) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ depth power,
      moment depth power ≤ constant ^ power * (power.factorial : ℝ) := by
  classical
  obtain ⟨initialConstant, initialConstantAtLeastOne, initialValid⟩ := initialBound
  obtain ⟨threshold, preservation⟩ := eventualPreservation
  choose bound boundValid using naturalBounds
  let constant := initialConstant + ∑ order ∈ Finset.range threshold, max 0 (bound order)
  have sumNonnegative : 0 ≤ ∑ order ∈ Finset.range threshold, max 0 (bound order) :=
    Finset.sum_nonneg (fun order _ => le_max_left _ _)
  have initialConstantBound : initialConstant ≤ constant := by dsimp [constant]; linarith
  have constantAtLeastOne : 1 ≤ constant := initialConstantAtLeastOne.trans initialConstantBound
  have lowOrderBound (order : ℕ) (orderSmall : order < threshold) : bound order ≤ constant := by
    have comparison := Finset.single_le_sum (s := Finset.range threshold)
      (f := fun order => max 0 (bound order)) (fun order _ => le_max_left 0 (bound order))
      (Finset.mem_range.mpr orderSmall)
    have := le_max_right 0 (bound order)
    dsimp [constant]
    linarith
  refine ⟨constant, constantAtLeastOne, ?_⟩
  intro depth
  induction depth with
  | zero =>
      intro power
      exact (initialValid power).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans initialConstantAtLeastOne) initialConstantBound power)
        (Nat.cast_nonneg _))
  | succ depth inductionHypothesis =>
      intro power
      by_cases powerSmall : power < threshold
      · by_cases powerZero : power = 0
        · subst power; simp [zeroOrder]
        · have constantPowerBound : constant ≤ constant ^ power := by
            simpa only [pow_one] using pow_le_pow_right₀ constantAtLeastOne (Nat.pos_of_ne_zero powerZero)
          exact ((boundValid power (depth + 1)).trans (lowOrderBound power powerSmall)).trans
            (constantPowerBound.trans (le_mul_of_one_le_right
              (pow_nonneg (zero_le_one.trans constantAtLeastOne) power)
              (by exact_mod_cast Nat.factorial_pos power)))
      · exact preservation power (Nat.le_of_not_gt powerSmall) depth constant constantAtLeastOne
          (fun order _ => inductionHypothesis order)

end IGSIII.Chemical.SmallBall
