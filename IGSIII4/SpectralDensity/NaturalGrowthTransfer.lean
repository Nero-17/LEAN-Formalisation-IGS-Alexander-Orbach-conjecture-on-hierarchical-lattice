import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter

theorem exponential_growth_lower_of_power_bounds
    (scale : ℕ → ℝ) (lower growth constant : ℝ)
    (lowerPositive : 0 < lower) (growthPositive : 0 < growth)
    (lowerBound : ∀ depth, lower ^ depth ≤ scale depth)
    (upperBound : ∀ depth, scale depth ≤ constant * growth ^ depth) : lower ≤ growth := by
  by_contra notBelow
  have ratioAboveOne : 1 < lower / growth := (one_lt_div growthPositive).mpr (lt_of_not_ge notBelow)
  have bounded (depth : ℕ) : (lower / growth) ^ depth ≤ constant := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos growthPositive depth)).mpr
      ((lowerBound depth).trans (upperBound depth))
  have divergent := tendsto_pow_atTop_atTop_of_one_lt ratioAboveOne
  obtain ⟨depth, beyond⟩ := (divergent.eventually (eventually_gt_atTop constant)).exists
  exact (not_lt_of_ge (bounded depth)) beyond

theorem actual_natural_growth_lower_of_finite_scale_bounds
    (rule : Universality.Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : rule.network.reliability probability = probability)
    (natural : IGSIII34.Percolation.NaturalResistanceCompletion rule probability positive belowOne critical)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (finiteBounds : ∀ depth, lower ^ depth ≤
      (IGSIII34.Percolation.electricalOrbitScale rule probability positive belowOne critical depth : ℝ)) :
    lower ≤ natural.growth := by
  obtain ⟨constant, _, bounds, _, _⟩ :=
    IGSIII34.Percolation.natural_physical_omega_witness_completion
      rule classicalRule probability positive belowOne critical natural
  exact exponential_growth_lower_of_power_bounds _ lower natural.growth constant⁻¹
    lowerPositive (zero_lt_one.trans natural.aboveOne) finiteBounds (fun depth => (bounds depth).2)

theorem actual_natural_growth_le_unit_mean
    (rule : Universality.Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : rule.network.reliability probability = probability)
    (natural : IGSIII34.Percolation.NaturalResistanceCompletion rule probability positive belowOne critical) :
    natural.growth ≤
      (IGSIII34.Percolation.electricalOrbitScale rule probability positive belowOne critical 1 : ℝ) := by
  obtain ⟨_, _, bounds, _, _⟩ :=
    IGSIII34.Percolation.natural_physical_omega_witness_completion
      rule classicalRule probability positive belowOne critical natural
  simpa only [pow_one] using (bounds 1).1

end
end IGSIII4.SpectralDensity
