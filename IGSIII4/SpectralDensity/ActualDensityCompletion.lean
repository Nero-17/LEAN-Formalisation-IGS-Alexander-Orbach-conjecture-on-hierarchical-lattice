import IGSIII4.SpectralDensity.ActualMomentUniformInvariant
import IGSIII4.SpectralDensity.ActualUnitNaturalUpper

/-! The actual finite-input moment estimates imply two-sided bounds for the
same natural resistance completion used by the physical typical-point
theorem. All moment and resistance premises of the density adapter are
discharged here. The finite prefix retains the length-two patch. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34 IGSIII34.Percolation Filter Topology

theorem appendix_actual_natural_growth_lower (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (blockCount base length : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2)) ≤
        (appendixNaturalCompletion base length).growth := by
  filter_upwards [appendix_finite_cell_moment_bounds_eventually base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length cellBounds lengthLarge
  have pathsPositive : 0 < pathCount (max length 2) := Nat.ceil_pos.mpr (by
    have : (0 : ℝ) < (max length 2 : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_max_right length 2))
    positivity : 0 < ((max length 2 : ℕ) : ℝ) * (4 / 3 : ℝ) ^ max length 2)
  have blocksPositive : 0 < (blockCount base (max length 2) : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity : 0 < base ^ max length 2) :
      0 < blockCount base (max length 2))
  have bound := actual_natural_growth_lower_of_uniform_cell_moments
    (blockCount base (max length 2)) (pathCount (max length 2)) (max length 2 - 2) pathsPositive
    (appendixCriticalProbability base (max length 2))
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2
    (appendixNaturalCompletion base length)
    ((blockCount base (max length 2) : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2)))
    (by positivity)
    (by rw [max_eq_left lengthLarge]; exact cellBounds)
  simpa only [max_eq_left lengthLarge] using bound

theorem appendix_actual_natural_growth_bounds (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))) * (blockCount base length : ℝ) ≤
          (appendixNaturalCompletion base length).growth ∧
        (appendixNaturalCompletion base length).growth ≤
          (2 + 8 / Real.log base) * (blockCount base length : ℝ) := by
  filter_upwards [appendix_actual_natural_growth_lower base baseAboveOne,
    appendix_actual_natural_growth_upper base baseAboveOne] with length lower upper
  exact ⟨by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using lower, upper⟩

theorem appendix_actual_natural_dimension_limit (base : ℝ) (baseAboveOne : 1 < base) :
    Tendsto (fun length => typicalSpectralDimension
      (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
      (appendixNaturalCompletion base length).growth) atTop (𝓝 (limitingDimension base)) := by
  apply appendix_natural_dimension_limit_of_resistance_bounds base baseAboveOne
    (1 / (40 * ((⌈base⌉₊ : ℝ) + 2))) (2 + 8 / Real.log base)
  · positivity
  · have := Real.log_pos baseAboveOne
    positivity
  · exact appendix_actual_natural_growth_bounds base baseAboveOne

/-- Every nonempty open subinterval of (1,2) is met by the explicit finite
appendix family, at its own critical probability and its selected natural
resistance completion. -/
theorem appendix_actual_spectral_density
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ base : ℝ, 1 < base ∧ ∃ length : ℕ,
      typicalSpectralDimension
        (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
        (appendixNaturalCompletion base length).growth ∈ Set.Ioo lower upper := by
  obtain ⟨base, baseAboveOne, baseValue⟩ := limitingDimension_surjective_Ioo
    ((lower + upper) / 2) (by linarith) (by linarith)
  have inInterval : Set.Ioo lower upper ∈ 𝓝 (limitingDimension base) := by
    rw [baseValue]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨length, dimensionInInterval⟩ :=
    ((appendix_actual_natural_dimension_limit base baseAboveOne).eventually inInterval).exists
  exact ⟨base, baseAboveOne, length, dimensionInInterval⟩

/-- Unconditional spectral density for actual classical finite rules. The
more specific appendix witness is retained by the preceding theorem. -/
theorem actual_spectral_density
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ dimension ∈ actualClassicalSpectralDimensions, dimension ∈ Set.Ioo lower upper := by
  obtain ⟨base, _, length, dimensionInInterval⟩ :=
    appendix_actual_spectral_density lower upper lowerAboveOne upperBelowTwo nonemptyInterval
  exact ⟨_, appendix_natural_dimension_mem base length, dimensionInInterval⟩

end
end IGSIII4.SpectralDensity.ActualFamily
