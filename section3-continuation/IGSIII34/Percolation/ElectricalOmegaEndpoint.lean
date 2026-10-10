import IGSIII34.Percolation.ElectricalGapDominance
import IGSIII.Probability.LpComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal _root_.Topology
theorem electricalOmega_has_fixed_ray_upper_endpoint (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthAboveOne : 1 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ (electricalOrbitScale rule p positive lessOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive lessOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedIdentity : normalizedElectricalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed)
    (fixedPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower)
    (lowerBound : ∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth, lower • fixed ≤ value)
    (upperBound : ∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth, value ≤ upper • fixed) :
    ∃ scalar : ℝ, 0 < scalar ∧ scalar • fixed ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth ∧
      (∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth, value ≤ scalar • fixed) ∧
      ∀ competitor : ℝ, (∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth,
        value ≤ competitor • fixed) → scalar ≤ competitor := by
  have growthPositive : 0 < growth := zero_lt_one.trans growthAboveOne
  obtain ⟨nonempty, compact, mapsTo, onto⟩ := electricalOmegaSet_properties rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds
  have familyPositive (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
      (membership : value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth) :
      ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < value marks := by
    filter_upwards [fixedPositive, (Lp.coeFn_le _ _).mpr (lowerBound value membership), Lp.coeFn_smul lower fixed]
      with marks positive inequality scalarEquality
    rw [scalarEquality, Pi.smul_apply, smul_eq_mul] at inequality
    exact (mul_pos lowerPositive positive).trans_le inequality
  have familyNonnegative : ∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth, 0 ≤ value := by
    intro value membership
    exact (Lp.coeFn_nonneg value).mp ((familyPositive value membership).mono (fun _ positive => positive.le))
  obtain ⟨scalar, scalarNonnegative, dominates, least⟩ := exists_least_lp_domination_scalar
    (electricalOmegaSet rule p positive lessOne fixedPoint growth) nonempty fixed fixedPositive familyPositive upper upperBound
  have scalarPositive : 0 < scalar := by
    obtain ⟨value, membership⟩ := nonempty
    have positiveAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < scalar := by
      filter_upwards [familyPositive value membership, fixedPositive,
        (Lp.coeFn_le _ _).mpr (dominates value membership), Lp.coeFn_smul scalar fixed]
        with marks valuePositive basePositive comparison scalarEquality
      rw [scalarEquality, Pi.smul_apply, smul_eq_mul] at comparison
      by_contra nonpositive
      exact (valuePositive.trans_le comparison).not_ge
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt nonpositive) basePositive.le)
    obtain ⟨_, positive⟩ := positiveAe.exists
    exact positive
  refine ⟨scalar, scalarPositive, ?_, dominates, least⟩
  by_contra absent
  have upperFixed : normalizedElectricalTransferLp rule p positive lessOne fixedPoint 2 growth (scalar • fixed) = scalar • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive lessOne fixedPoint 2 growth scalar scalarNonnegative, fixedIdentity]
  obtain ⟨base, baseMembership⟩ := nonempty
  obtain ⟨scale, scaleAtLeastOne, gapDominates⟩ := invariant_gap_dominates_electrical_cluster rule classical
    p positive lessOne fixedPoint growth growthAboveOne (electricalOmegaSet rule p positive lessOne fixedPoint growth)
    compact familyNonnegative mapsTo onto (scalar • fixed) upperFixed dominates absent base baseMembership
  have scalePositive : 0 < scale := zero_lt_one.trans_le scaleAtLeastOne
  have smallerDomination : ∀ value ∈ electricalOmegaSet rule p positive lessOne fixedPoint growth,
      value ≤ (scalar - scale⁻¹ * lower) • fixed := by
    intro value membership
    have gapLower := (lp_smul_mono (lowerBound base baseMembership) scale⁻¹ (inv_nonneg.mpr scalePositive.le)).trans
      (lp_smul_mono (gapDominates value membership) scale⁻¹ (inv_nonneg.mpr scalePositive.le))
    simp only [smul_smul, inv_mul_cancel₀ scalePositive.ne', one_smul] at gapLower
    rw [sub_smul]
    apply le_sub_iff_add_le.mpr
    simpa only [add_comm] using le_sub_iff_add_le.mp gapLower
  have contradiction := least (scalar - scale⁻¹ * lower) smallerDomination
  have positiveGap : 0 < scale⁻¹ * lower := mul_pos (inv_pos.mpr scalePositive) lowerPositive
  linarith


end
end IGSIII34.Percolation


