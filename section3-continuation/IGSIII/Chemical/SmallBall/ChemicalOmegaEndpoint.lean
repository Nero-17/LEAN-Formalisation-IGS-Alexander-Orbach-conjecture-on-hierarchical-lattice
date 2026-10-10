import IGSIII.Chemical.SmallBall.InvariantGapPathBarrier
import IGSIII.Chemical.SmallBall.ChemicalOmegaMoments
import IGSIII.Probability.LpComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Set IGSIII.Probability Filter
open scoped ENNReal Topology

noncomputable section

theorem invariant_gap_dominates_chemical_cluster (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)))
    (compact : IsCompact family) (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family)
    (base : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (baseMembership : base ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    ∃ scale : ℝ, 1 ≤ scale ∧ ∀ value ∈ family, base ≤ scale • (upper - value) := by
  have countPositive : (0 : ℝ) < (((rule.edges + 3) ^ 4 : ℕ) : ℝ) := by positivity
  have ratioPositive : 0 < (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ := inv_pos.mpr (by positivity)
  have geometricIdentity : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ = 1 / 2 := by field_simp
  have geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ < 1 := by rw [geometricIdentity]; norm_num
  obtain ⟨scale, scaleAtLeastOne, barrier⟩ := exists_uniform_invariant_gap_unit_barrier rule classical
    p positive lessOne fixedPoint growth growthPositive family compact familyNonnegative mapsTo onto upper upperFixed upperBound absent
    ratioPositive geometricBelowOne
  have summable := (summable_nat_add_iff 1).mpr
    ((geometric_power_geometric_summable classical.scale
      (mul_nonneg (Nat.cast_nonneg _) ratioPositive.le) geometricBelowOne).div_const
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹))
  have shiftedCluster : MapClusterPt base atTop
      (chemicalOrbit rule p positive lessOne fixedPoint growth ∘ (fun depth => depth + 1)) := by
    rw [mapClusterPt_comp, Filter.map_add_atTop_eq_nat]
    exact baseMembership
  obtain ⟨subsequence, increasing, convergence⟩ := shiftedCluster.tendsto_subseq
  obtain ⟨subsubsequence, subIncreasing, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp convergence).exists_seq_tendsto_ae
  refine ⟨scale, scaleAtLeastOne, fun value membership => ?_⟩
  have finiteEvents : (∑' depth : ℕ, (independentInnovationLaw rule p positive lessOne fixedPoint)
      {marks | scale * (upper - value) marks < chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1) marks}) ≠ ∞ := by
    apply ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro depth
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (barrier value membership depth)
  have eventual := ae_eventually_notMem finiteEvents
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [pointwise, eventual, Lp.coeFn_smul scale (upper - value)]
    with marks limit eventuallyBound scalarEquality
  rw [scalarEquality, Pi.smul_apply, smul_eq_mul]
  apply le_of_tendsto limit
  have along := (increasing.tendsto_atTop.comp subIncreasing.tendsto_atTop).eventually eventuallyBound
  exact along.mono (fun depth outside => not_lt.mp outside)

theorem chemicalOmega_has_fixed_ray_upper_endpoint (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedIdentity : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed)
    (fixedPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower)
    (lowerBound : ∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth, lower • fixed ≤ value)
    (upperBound : ∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth, value ≤ upper • fixed) :
    ∃ scalar : ℝ, 0 < scalar ∧ scalar • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth ∧
      (∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth, value ≤ scalar • fixed) ∧
      ∀ competitor : ℝ, (∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
        value ≤ competitor • fixed) → scalar ≤ competitor := by
  obtain ⟨nonempty, compact, mapsTo, onto⟩ := chemicalOmegaSet_properties rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds
  have familyPositive (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
      (membership : value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
      ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < value marks := by
    filter_upwards [fixedPositive, (Lp.coeFn_le _ _).mpr (lowerBound value membership), Lp.coeFn_smul lower fixed]
      with marks positive inequality scalarEquality
    rw [scalarEquality, Pi.smul_apply, smul_eq_mul] at inequality
    exact (mul_pos lowerPositive positive).trans_le inequality
  have familyNonnegative : ∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth, 0 ≤ value := by
    intro value membership
    exact (Lp.coeFn_nonneg value).mp ((familyPositive value membership).mono (fun _ positive => positive.le))
  obtain ⟨scalar, scalarNonnegative, dominates, least⟩ := exists_least_lp_domination_scalar
    (chemicalOmegaSet rule p positive lessOne fixedPoint growth) nonempty fixed fixedPositive familyPositive upper upperBound
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
  have upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth (scalar • fixed) = scalar • fixed := by
    rw [normalizedChemicalTransferLp_smul rule p positive lessOne fixedPoint 2 growth scalar scalarNonnegative, fixedIdentity]
  obtain ⟨base, baseMembership⟩ := nonempty
  obtain ⟨scale, scaleAtLeastOne, gapDominates⟩ := invariant_gap_dominates_chemical_cluster rule classical
    p positive lessOne fixedPoint growth growthPositive (chemicalOmegaSet rule p positive lessOne fixedPoint growth)
    compact familyNonnegative mapsTo onto (scalar • fixed) upperFixed dominates absent base baseMembership
  have scalePositive : 0 < scale := zero_lt_one.trans_le scaleAtLeastOne
  have smallerDomination : ∀ value ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
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
end IGSIII.Chemical.SmallBall
