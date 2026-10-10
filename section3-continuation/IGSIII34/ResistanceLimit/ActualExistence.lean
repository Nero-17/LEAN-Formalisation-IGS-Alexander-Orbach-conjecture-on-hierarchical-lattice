import IGSIII34.ResistanceLimit.ActualCompactness

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

/-- The actual model supplies a compact electrical completion almost surely,
with growth between the pivotal lower bound and the path-length upper bound. -/
theorem exists_actual_compact_electrical_completion
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ growth : ℝ, ∃ growthGreaterThanOne : 1 < growth,
      ∃ endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        deriv rule.network.reliability p ≤ growth ∧
        growth ≤ ∫ configuration, (pathLength configuration : ℝ)
          ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
        ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∃ typical : StationaryElectricalTypical rule p positive belowOne fixedPoint growth endpoint marks,
            CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth endpoint
              (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩) := by
  obtain ⟨constant, growth, constantPositive, _, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, _, _, amplitude, amplitudeLower, membership, _, _⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthGreaterThanOne :=
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale).trans_le growthLower
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth
      (amplitude • fixed) = amplitude • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth amplitude
      (zero_le_one.trans amplitudeLower), fixedIdentity]
  have inverseBelowOne : growth⁻¹ < 1 := (inv_lt_one₀ growthPositive).mpr growthGreaterThanOne
  obtain ⟨eta, etaLower, etaBelowOne⟩ := exists_between inverseBelowOne
  have etaPositive := (inv_pos.mpr growthPositive).trans etaLower
  have productGreaterThanOne : 1 < growth * eta := by
    have bound := (div_lt_iff₀ growthPositive).mp (show 1 / growth < eta by simpa only [one_div] using etaLower)
    simpa only [mul_comm] using bound
  exact ⟨growth, growthGreaterThanOne, amplitude • fixed, growthLower, growthUpper,
    ae_actualStationaryElectricalSpace_compact_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthGreaterThanOne growthBounds (amplitude • fixed) endpointFixed membership
      eta etaPositive etaBelowOne productGreaterThanOne⟩

end
end IGSIII34.ResistanceLimit
