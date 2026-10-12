import IGSIII4.SpectralDensity.LimitingDimensionGeometry
import IGSIII4.SpectralDensity.ActualPhysicalDensity

/-! Rational parameters already give the Appendix C density witnesses,
including the physical typical-point exponent of the same natural
resistance completion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open IGSIII34 Filter Topology

theorem appendix_actual_spectral_density_rational_base_eventually
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ base : ℚ, 1 < base ∧ ∀ᶠ length : ℕ in atTop,
      typicalSpectralDimension
        (actualMassGrowth (appendixRule (base : ℝ) (max length 2))
          (appendixCriticalProbability (base : ℝ) (max length 2)))
        (appendixNaturalCompletion (base : ℝ) length).growth ∈ Set.Ioo lower upper := by
  obtain ⟨base, baseAboveOne, limitingValue⟩ :=
    rational_limitingDimension_mem_interval lower upper lowerAboveOne upperBelowTwo nonemptyInterval
  have baseRealAboveOne : (1 : ℝ) < (base : ℝ) := by exact_mod_cast baseAboveOne
  refine ⟨base, baseAboveOne, ?_⟩
  exact (appendix_actual_natural_dimension_limit (base : ℝ) baseRealAboveOne).eventually
    (Ioo_mem_nhds limitingValue.1 limitingValue.2)

theorem actual_physical_spectral_density_rational_base
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) (minimumLength : ℕ) :
    ∃ base : ℚ, 1 < base ∧ ∃ length : ℕ, max minimumLength 2 ≤ length ∧
      (appendixRule (base : ℝ) (max length 2)).Classical ∧
      (appendixRule (base : ℝ) (max length 2)).network.fullGraph.dist
        (appendixRule (base : ℝ) (max length 2)).network.source
        (appendixRule (base : ℝ) (max length 2)).network.target = 2 ∧
      (appendixRule (base : ℝ) (max length 2)).network.fullGraph.degree
        (appendixRule (base : ℝ) (max length 2)).network.source = 2 ∧
      (appendixRule (base : ℝ) (max length 2)).network.fullGraph.degree
        (appendixRule (base : ℝ) (max length 2)).network.target = 2 ∧
      (appendixRule (base : ℝ) (max length 2)).network.terminalEdgeConnectivity = 2 ∧
      0 < appendixCriticalProbability (base : ℝ) (max length 2) ∧
      appendixCriticalProbability (base : ℝ) (max length 2) < 1 ∧
      (appendixRule (base : ℝ) (max length 2)).network.reliability
        (appendixCriticalProbability (base : ℝ) (max length 2)) =
          appendixCriticalProbability (base : ℝ) (max length 2) ∧
      typicalSpectralDimension
        (actualMassGrowth (appendixRule (base : ℝ) (max length 2))
          (appendixCriticalProbability (base : ℝ) (max length 2)))
        (appendixNaturalCompletion (base : ℝ) length).growth ∈ Set.Ioo lower upper ∧
      ActualPhysicalTypicalSpectralDimension
        (appendixRule (base : ℝ) (max length 2))
        (appendixCriticalProbability (base : ℝ) (max length 2))
        (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).1
        (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).2.1
        (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).2.2
        (appendixNaturalCompletion (base : ℝ) length)
        (typicalSpectralDimension
          (actualMassGrowth (appendixRule (base : ℝ) (max length 2))
            (appendixCriticalProbability (base : ℝ) (max length 2)))
          (appendixNaturalCompletion (base : ℝ) length).growth) := by
  obtain ⟨base, baseAboveOne, eventualDimension⟩ :=
    appendix_actual_spectral_density_rational_base_eventually lower upper
      lowerAboveOne upperBelowTwo nonemptyInterval
  obtain ⟨length, dimensionInInterval, lengthLarge⟩ :=
    (eventualDimension.and (eventually_ge_atTop (max minimumLength 2))).exists
  obtain ⟨distance, sourceDegree, targetDegree, connectivity⟩ :=
    appendixRule_terminal_parameters (base : ℝ) (max length 2) (Nat.le_max_right _ _)
  exact ⟨base, baseAboveOne, length, lengthLarge,
    appendixRule_classical (base : ℝ) _ (Nat.le_max_right _ _),
    distance, sourceDegree, targetDegree, connectivity,
    (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).1,
    (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).2.1,
    (appendixCriticalProbability_spec (base : ℝ) _ (Nat.le_max_right _ _)).2.2,
    dimensionInInterval, appendix_actual_physical_typical_dimension (base : ℝ) length⟩

end
end IGSIII4.SpectralDensity.ActualFamily
