import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Growth normalization from a bounded multiplicative defect.  The hypotheses
are finite-level mean inequalities, not an assumed eigenvalue or eigenlaw. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Filter Set
open scoped Topology

noncomputable section

theorem bounded_additive_defect_growth {sequence : ℕ → ℝ} {defect : ℝ}
    (zero : sequence 0 = 0) (nonnegative : ∀ depth, 0 ≤ sequence depth)
    (subadditive : Subadditive sequence) (defectNonnegative : 0 ≤ defect)
    (lowerAddition : ∀ first second,
      sequence first + sequence second - defect ≤ sequence (first + second)) :
    ∃ growth : ℝ, 0 ≤ growth ∧ ∀ depth : ℕ,
      (depth : ℝ) * growth ≤ sequence depth ∧
        sequence depth ≤ (depth : ℝ) * growth + defect := by
  have lowerBounded : BddBelow (range (fun depth : ℕ => sequence depth / depth)) :=
    ⟨0, by rintro _ ⟨depth, rfl⟩; exact div_nonneg (nonnegative depth) (Nat.cast_nonneg depth)⟩
  have upperBound (depth : ℕ) : sequence depth ≤ (depth : ℝ) * sequence 1 := by
    simpa only [Nat.mul_one, Nat.add_zero, zero, add_zero] using
      subadditive.apply_mul_add_le depth 1 0
  have reflectedSubadditive : Subadditive (fun depth => defect - sequence depth) := by
    intro first second
    have lower := lowerAddition first second
    linarith
  have reflectedLowerBounded :
      BddBelow (range (fun depth : ℕ => (defect - sequence depth) / depth)) := by
    refine ⟨-sequence 1, ?_⟩
    rintro _ ⟨depth, rfl⟩
    by_cases depthZero : depth = 0
    · subst depth
      simp only [Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (nonnegative 1)
    · have depthPositive : (0 : ℝ) < depth := Nat.cast_pos.mpr (Nat.pos_of_ne_zero depthZero)
      apply (le_div_iff₀ depthPositive).mpr
      have upper := upperBound depth
      nlinarith
  have constantRatio : Tendsto (fun depth : ℕ => defect / (depth : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have reflectedConvergence :
      Tendsto (fun depth : ℕ => (defect - sequence depth) / depth) atTop
        (𝓝 (-subadditive.lim)) := by
    simpa only [sub_div, zero_sub] using
      constantRatio.sub (subadditive.tendsto_lim lowerBounded)
  have reflectedLimit : reflectedSubadditive.lim = -subadditive.lim :=
    tendsto_nhds_unique (reflectedSubadditive.tendsto_lim reflectedLowerBounded)
      reflectedConvergence
  refine ⟨subadditive.lim, ?_, ?_⟩
  · exact ge_of_tendsto (subadditive.tendsto_lim lowerBounded)
      (Eventually.of_forall (fun depth => div_nonneg (nonnegative depth) (Nat.cast_nonneg depth)))
  · intro depth
    by_cases depthZero : depth = 0
    · subst depth
      simp only [Nat.cast_zero, zero_mul, zero, zero_add, le_refl, true_and]
      exact defectNonnegative
    · have depthPositive : (0 : ℝ) < depth := Nat.cast_pos.mpr (Nat.pos_of_ne_zero depthZero)
      have lower := (le_div_iff₀ depthPositive).mp
        (subadditive.lim_le_div lowerBounded depthZero)
      have upper := reflectedSubadditive.lim_le_div reflectedLowerBounded depthZero
      rw [reflectedLimit, le_div_iff₀ depthPositive] at upper
      constructor <;> nlinarith

theorem quasi_multiplicative_growth {means : ℕ → ℝ} {constant : ℝ}
    (zero : means 0 = 1) (atLeastOne : ∀ depth, 1 ≤ means depth)
    (constantPositive : 0 < constant) (constantAtMostOne : constant ≤ 1)
    (upperProduct : ∀ first second, means (first + second) ≤ means first * means second)
    (lowerProduct : ∀ first second,
      constant * means first * means second ≤ means (first + second)) :
    ∃ growth : ℝ, 1 ≤ growth ∧ ∀ depth : ℕ,
      growth ^ depth ≤ means depth ∧ means depth ≤ constant⁻¹ * growth ^ depth := by
  have positive (depth : ℕ) : 0 < means depth := zero_lt_one.trans_le (atLeastOne depth)
  have logarithmicSubadditive : Subadditive (fun depth => Real.log (means depth)) := by
    intro first second
    have inequality := Real.log_le_log (positive (first + second)) (upperProduct first second)
    rwa [Real.log_mul (positive first).ne' (positive second).ne'] at inequality
  have logarithmicLower : ∀ first second,
      Real.log (means first) + Real.log (means second) - (-Real.log constant) ≤
        Real.log (means (first + second)) := by
    intro first second
    have inequality := Real.log_le_log
      (mul_pos (mul_pos constantPositive (positive first)) (positive second))
      (lowerProduct first second)
    rw [Real.log_mul (mul_pos constantPositive (positive first)).ne' (positive second).ne',
      Real.log_mul constantPositive.ne' (positive first).ne'] at inequality
    linarith
  obtain ⟨growth, growthNonnegative, bounds⟩ := bounded_additive_defect_growth
    (by simp [zero]) (fun depth => Real.log_nonneg (atLeastOne depth))
    logarithmicSubadditive (neg_nonneg.mpr (Real.log_nonpos constantPositive.le constantAtMostOne))
    logarithmicLower
  refine ⟨Real.exp growth, ?_, ?_⟩
  · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr growthNonnegative
  · intro depth
    constructor
    · have bound := Real.exp_le_exp.mpr (bounds depth).1
      simpa only [Real.exp_nat_mul, Real.exp_log (positive depth)] using bound
    · have bound := Real.exp_le_exp.mpr (bounds depth).2
      rw [Real.exp_log (positive depth), Real.exp_add, Real.exp_nat_mul,
        Real.exp_neg, Real.exp_log constantPositive] at bound
      simpa only [mul_comm] using bound

theorem base_le_of_uniform_pow_comparison {first second constant : ℝ}
    (secondPositive : 0 < second)
    (comparison : ∀ depth : ℕ, first ^ depth ≤ constant * second ^ depth) : first ≤ second := by
  by_contra unordered
  have ratioAboveOne : 1 < first / second := (one_lt_div secondPositive).mpr (lt_of_not_ge unordered)
  obtain ⟨depth, exceeds⟩ := pow_unbounded_of_one_lt constant ratioAboveOne
  have bounded : (first / second) ^ depth ≤ constant := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos secondPositive depth)).mpr (comparison depth)
  exact (not_lt_of_ge bounded) exceeds

theorem quasi_multiplicative_growth_between {means : ℕ → ℝ} {constant lower upper : ℝ}
    (zero : means 0 = 1) (lowerAtLeastOne : 1 ≤ lower)
    (lowerBound : ∀ depth : ℕ, lower ^ depth ≤ means depth)
    (upperBound : ∀ depth : ℕ, means depth ≤ upper ^ depth)
    (constantPositive : 0 < constant) (constantAtMostOne : constant ≤ 1)
    (upperProduct : ∀ first second, means (first + second) ≤ means first * means second)
    (lowerProduct : ∀ first second,
      constant * means first * means second ≤ means (first + second)) :
    ∃ growth : ℝ, lower ≤ growth ∧ growth ≤ upper ∧ ∀ depth : ℕ,
      growth ^ depth ≤ means depth ∧ means depth ≤ constant⁻¹ * growth ^ depth := by
  obtain ⟨growth, growthAtLeastOne, bounds⟩ := quasi_multiplicative_growth zero
    (fun depth => (one_le_pow₀ lowerAtLeastOne).trans (lowerBound depth))
    constantPositive constantAtMostOne upperProduct lowerProduct
  refine ⟨growth, ?_, ?_, bounds⟩
  · exact base_le_of_uniform_pow_comparison (zero_lt_one.trans_le growthAtLeastOne)
      (fun depth => (lowerBound depth).trans (bounds depth).2)
  · simpa only [pow_one] using (bounds 1).1.trans (upperBound 1)

end
end IGSIII.Chemical.SmallBall
