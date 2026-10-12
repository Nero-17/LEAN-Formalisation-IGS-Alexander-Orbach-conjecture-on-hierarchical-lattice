import IGSIII4.SpectralDensity.ActualMassGrowth
import IGSIII4.SpectralDensity.Asymptotics
import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion
import IGSIII4.ActualTypicalPointSectionFour

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34 IGSIII34.Percolation Filter Topology

/-- Dimensions of actual natural completions at the rule's own interior critical point.
The imported actual heat-kernel theorem identifies these numerical values with
the physical-mass typical exponents. -/
def actualClassicalSpectralDimensions : Set ℝ :=
  {dimension | ∃ finiteRule : Rule, finiteRule.Classical ∧
    ∃ probability : ℝ, ∃ positive : 0 < probability, ∃ belowOne : probability < 1,
      ∃ critical : finiteRule.network.reliability probability = probability,
      ∃ natural : NaturalResistanceCompletion finiteRule probability positive belowOne critical,
        dimension = typicalSpectralDimension (actualMassGrowth finiteRule probability) natural.growth}

/-- A finite initial prefix is replaced by length two, so every sequence entry
is a classical rule; the large-length family is unchanged. -/
def appendixNaturalCompletion (base : ℝ) (length : ℕ) :
    NaturalResistanceCompletion (appendixRule base (max length 2))
      (appendixCriticalProbability base (max length 2))
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2 :=
  Classical.choice (exists_natural_resistance_completion
    (appendixRule base (max length 2)) (appendixRule_classical base _ (Nat.le_max_right _ _))
    (appendixCriticalProbability base (max length 2))
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2)

theorem appendix_natural_dimension_mem (base : ℝ) (length : ℕ) :
    typicalSpectralDimension
      (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
      (appendixNaturalCompletion base length).growth ∈ actualClassicalSpectralDimensions := by
  exact ⟨appendixRule base (max length 2), appendixRule_classical base _ (Nat.le_max_right _ _),
    appendixCriticalProbability base (max length 2),
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1,
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1,
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2,
    appendixNaturalCompletion base length, rfl⟩

theorem appendix_patched_actual_mass_normalized_log_limit (base : ℝ) (baseAboveOne : 1 < base) :
    Tendsto (fun length => Real.log (actualMassGrowth (appendixRule base (max length 2))
      (appendixCriticalProbability base (max length 2))) / (length : ℝ))
      atTop (𝓝 (Real.log base + Real.log (4 / 3 : ℝ))) := by
  apply (appendix_actual_mass_normalized_log_limit base baseAboveOne).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with length lengthLarge
  simp only [max_eq_left lengthLarge]

theorem appendix_natural_dimension_limit_of_resistance_bounds
    (base : ℝ) (baseAboveOne : 1 < base)
    (lowerCoefficient upperCoefficient : ℝ)
    (lowerPositive : 0 < lowerCoefficient) (upperPositive : 0 < upperCoefficient)
    (resistanceBounds : ∀ᶠ length : ℕ in atTop,
      lowerCoefficient * (blockCount base length : ℝ) ≤ (appendixNaturalCompletion base length).growth ∧
      (appendixNaturalCompletion base length).growth ≤ upperCoefficient * (blockCount base length : ℝ)) :
    Tendsto (fun length => typicalSpectralDimension
      (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
      (appendixNaturalCompletion base length).growth) atTop (𝓝 (limitingDimension base)) := by
  apply spectral_limit_of_density_growth_rates base baseAboveOne
  · intro length
    exact zero_lt_one.trans (actualMassGrowth_above_one
      (appendixRule base (max length 2)) (appendixRule_classical base _ (Nat.le_max_right _ _))
      (appendixCriticalProbability base (max length 2))
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
      (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1)
  · intro length
    exact zero_lt_one.trans (appendixNaturalCompletion base length).aboveOne
  · exact appendix_patched_actual_mass_normalized_log_limit base baseAboveOne
  · exact resistance_normalized_log_limit_of_block_bounds base baseAboveOne _
      lowerCoefficient upperCoefficient lowerPositive upperPositive resistanceBounds

/-- This finishing adapter retains the actual resistance bounds as an explicit
premise until they are supplied by the finite-law moment proof. -/
theorem actual_spectral_density_of_appendix_resistance_bounds
    (resistanceBounds : ∀ base : ℝ, 1 < base →
      ∃ lowerCoefficient upperCoefficient : ℝ,
        0 < lowerCoefficient ∧ 0 < upperCoefficient ∧
        ∀ᶠ length : ℕ in atTop,
          lowerCoefficient * (blockCount base length : ℝ) ≤ (appendixNaturalCompletion base length).growth ∧
          (appendixNaturalCompletion base length).growth ≤ upperCoefficient * (blockCount base length : ℝ))
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2) (nonemptyInterval : lower < upper) :
    ∃ dimension ∈ actualClassicalSpectralDimensions, dimension ∈ Set.Ioo lower upper := by
  apply intervals_hit_of_limitingDimension_limits actualClassicalSpectralDimensions _
    lower upper lowerAboveOne upperBelowTwo nonemptyInterval
  intro base baseAboveOne
  obtain ⟨lowerCoefficient, upperCoefficient, lowerPositive, upperPositive, bounds⟩ :=
    resistanceBounds base baseAboveOne
  refine ⟨fun length => typicalSpectralDimension
    (actualMassGrowth (appendixRule base (max length 2)) (appendixCriticalProbability base (max length 2)))
    (appendixNaturalCompletion base length).growth, appendix_natural_dimension_mem base, ?_⟩
  exact appendix_natural_dimension_limit_of_resistance_bounds base baseAboveOne
    lowerCoefficient upperCoefficient lowerPositive upperPositive bounds

end
end IGSIII4.SpectralDensity.ActualFamily
