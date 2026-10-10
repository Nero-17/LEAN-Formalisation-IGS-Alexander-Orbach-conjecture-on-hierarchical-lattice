import IGSIII34.Percolation.ElectricalAlmostSure
import IGSIII34.Percolation.ElectricalStationaryField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem exists_actual_electrical_almostSure_amplitudes
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) ∧
      ∃ fixed : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth fixed = fixed ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < fixed marks) ∧
        (∫ marks, fixed marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        ∃ amplitude : ℝ, 1 ≤ amplitude ∧
          Tendsto (electricalOrbitLp rule p positive belowOne fixedPoint growth) atTop (𝓝 (amplitude • fixed)) ∧
          (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
            ∀ address : List (Fin rule.edges),
              Tendsto (fun depth => growth⁻¹^depth*electricalIteration rule marks depth address) atTop
                (𝓝 (amplitude*electricalField rule p positive belowOne fixedPoint fixed address marks))) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, amplitude, amplitudeLower, membership, dominates, least⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (amplitude • fixed) = amplitude • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth amplitude
      (zero_le_one.trans amplitudeLower), fixedIdentity]
  have convergence := electricalOrbitLp_tendsto_ae_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds (amplitude • fixed) endpointFixed membership
  have rootLimit : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => growth⁻¹^depth*electricalIteration rule marks depth []) atTop (𝓝 (amplitude*fixed marks)) := by
    filter_upwards [convergence, ae_all_iff.mpr (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le),
      Lp.coeFn_smul amplitude fixed] with marks limit equalities scalarEquality
    simpa only [equalities, scalarEquality, Pi.smul_apply, smul_eq_mul] using limit
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, amplitude, amplitudeLower,
    electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth growthPositive
      growthBounds (amplitude • fixed) endpointFixed membership, ?_⟩
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootLimit
  simpa only [electricalIteration_shift, List.append_nil, electricalField] using shifted

end
end IGSIII34.Percolation
