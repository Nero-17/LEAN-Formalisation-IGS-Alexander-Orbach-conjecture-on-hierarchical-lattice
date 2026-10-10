import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace IGSIII.Mass

open MeasureTheory
open scoped BigOperators

/-- A scalar offspring generating function without extinction, and with a
positive probability of at least two children, has no fixed point in `(0,1)`.
The hypotheses concern the finite offspring law, not the desired conclusion. -/
theorem scalar_smoothing_zero_fixed_point
    {Branch : Type*} [Fintype Branch]
    (weight : Branch → ℝ) (children : Branch → ℕ)
    (weight_nonnegative : ∀ branch, 0 ≤ weight branch)
    (total_weight : ∑ branch, weight branch = 1)
    (no_extinction : ∀ branch, 1 ≤ children branch)
    (branching : ∃ branch, 0 < weight branch ∧ 1 < children branch)
    (zero_probability : ℝ) (nonnegative : 0 ≤ zero_probability)
    (below_one : zero_probability < 1)
    (smoothing : zero_probability = ∑ branch, weight branch * zero_probability ^ children branch) :
    zero_probability = 0 := by
  by_contra nonzero
  have positive : 0 < zero_probability := lt_of_le_of_ne nonnegative (Ne.symm nonzero)
  have strict : (∑ branch, weight branch * zero_probability ^ children branch) <
      ∑ branch, weight branch * zero_probability := by
    apply Finset.sum_lt_sum
    · intro branch _
      apply mul_le_mul_of_nonneg_left _ (weight_nonnegative branch)
      simpa only [pow_one] using
        (pow_right_strictAnti₀ positive below_one).antitone (no_extinction branch)
    · obtain ⟨branch, weight_positive, two_children⟩ := branching
      exact ⟨branch, Finset.mem_univ _,
        mul_lt_mul_of_pos_left (pow_lt_self_of_lt_one₀ positive below_one two_children) weight_positive⟩
  rw [← Finset.sum_mul, total_weight, one_mul, ← smoothing] at strict
  exact (lt_irrefl _ strict)

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

/-- The connected-child inequality used in Section 2 excludes every nonzero
zero-mass probability below one. -/
theorem zero_of_le_power (zero_probability : ℝ) (nonnegative : 0 ≤ zero_probability)
    (below_one : zero_probability < 1) (children : ℕ) (at_least_two : 1 < children)
    (connected_child_bound : zero_probability ≤ zero_probability ^ children) :
    zero_probability = 0 := by
  by_contra nonzero
  have positive : 0 < zero_probability := lt_of_le_of_ne nonnegative (Ne.symm nonzero)
  exact (not_lt_of_ge connected_child_bound)
    (pow_lt_self_of_lt_one₀ positive below_one at_least_two)

/-- A positive mean rules out an almost surely zero random variable. This is
the probabilistic step that removes the fixed point `q = 1`. -/
theorem zero_probability_lt_one_of_positive_mean [IsProbabilityMeasure probability]
    (limit : Ω → ℝ) (measurable : Measurable limit)
    (positive_mean : 0 < ∫ sample, limit sample ∂probability) :
    probability.real {sample | limit sample = 0} < 1 := by
  apply lt_of_le_of_ne measureReal_le_one
  intro equality
  have probability_one : probability {sample | limit sample = 0} = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp equality
  have zero_ae : limit =ᵐ[probability] 0 :=
    (mem_ae_iff_prob_eq_one (measurable (measurableSet_singleton 0))).mpr probability_one
  have integral_zero : (∫ sample, limit sample ∂probability) = 0 := by
    calc
      _ = ∫ sample, (0 : Ω → ℝ) sample ∂probability := integral_congr_ae zero_ae
      _ = 0 := by simp
  linarith

/-- The exact scalar zero-event smoothing equation, together with positive
mean and nonnegativity, implies strict positivity almost surely. Deriving this
equation for a particular multitype graph limit remains a separate obligation. -/
theorem ae_positive_of_scalar_smoothing
    [IsProbabilityMeasure probability] {Branch : Type*} [Fintype Branch]
    (weight : Branch → ℝ) (children : Branch → ℕ)
    (weight_nonnegative : ∀ branch, 0 ≤ weight branch)
    (total_weight : ∑ branch, weight branch = 1)
    (no_extinction : ∀ branch, 1 ≤ children branch)
    (branching : ∃ branch, 0 < weight branch ∧ 1 < children branch)
    (limit : Ω → ℝ) (measurable : Measurable limit)
    (nonnegative : ∀ᵐ sample ∂probability, 0 ≤ limit sample)
    (positive_mean : 0 < ∫ sample, limit sample ∂probability)
    (smoothing : probability.real {sample | limit sample = 0} =
      ∑ branch, weight branch * probability.real {sample | limit sample = 0} ^ children branch) :
    ∀ᵐ sample ∂probability, 0 < limit sample := by
  have probability_zero : probability {sample | limit sample = 0} = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    exact scalar_smoothing_zero_fixed_point weight children weight_nonnegative total_weight
      no_extinction branching _ (measureReal_nonneg)
      (zero_probability_lt_one_of_positive_mean limit measurable positive_mean) smoothing
  have nonzero : ∀ᵐ sample ∂probability, limit sample ≠ 0 := by
    simpa only [ae_iff, not_not] using probability_zero
  filter_upwards [nonnegative, nonzero] with sample lower different
  exact lt_of_le_of_ne lower (Ne.symm different)

/-- Positivity from the exact connected-descendant bound in the manuscript.
Its derivation from independent connected descendants is deliberately an
explicit input; the present theorem proves the zero-probability exclusion. -/
theorem ae_positive_of_connected_child_bound
    [IsProbabilityMeasure probability]
    (limit : Ω → ℝ) (measurable : Measurable limit)
    (nonnegative : ∀ᵐ sample ∂probability, 0 ≤ limit sample)
    (positive_mean : 0 < ∫ sample, limit sample ∂probability)
    (children : ℕ) (at_least_two : 1 < children)
    (connected_child_bound : probability.real {sample | limit sample = 0} ≤
      probability.real {sample | limit sample = 0} ^ children) :
    ∀ᵐ sample ∂probability, 0 < limit sample := by
  have probability_zero : probability {sample | limit sample = 0} = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    exact zero_of_le_power _ measureReal_nonneg
      (zero_probability_lt_one_of_positive_mean limit measurable positive_mean)
      children at_least_two connected_child_bound
  have nonzero : ∀ᵐ sample ∂probability, limit sample ≠ 0 := by
    simpa only [ae_iff, not_not] using probability_zero
  filter_upwards [nonnegative, nonzero] with sample lower different
  exact lt_of_le_of_ne lower (Ne.symm different)

end IGSIII.Mass
