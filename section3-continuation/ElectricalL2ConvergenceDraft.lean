import IGSIII34.Percolation.ElectricalFutureMean
import IGSIII34.Percolation.ElectricalEndpointSubsequence
import IGSIII34.Percolation.ElectricalActualEndpoint
import IGSIII34.Probability.LpOrbitStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth

include classical growthPositive growthBounds in
theorem electricalOrbitLp_tendsto_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    Tendsto W atTop (𝓝 endpoint) := by
  obtain ⟨subsequence, increasing, subsequenceConvergence, forward, backward⟩ :=
    exists_electrical_endpoint_comparison_subsequence rule classical p positive belowOne fixedPoint
      growth growthPositive (fun depth => (growthBounds depth).1) endpoint membership
  change Tendsto (fun depth => electricalComparisonCoefficient μ (W (subsequence depth)) endpoint) atTop (𝓝 0) at forward
  change Tendsto (fun depth => electricalComparisonCoefficient μ endpoint (W (subsequence depth))) atTop (𝓝 0) at backward
  let error : ℕ → ℝ := fun block =>
    electricalComparisonCoefficient μ (W (subsequence block)) endpoint * (∫ marks, endpoint marks ∂μ) +
      electricalComparisonCoefficient μ endpoint (W (subsequence block)) * constant⁻¹
  have errorConvergence : Tendsto error atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using
      (forward.mul_const (∫ marks, endpoint marks ∂μ)).add (backward.mul_const constant⁻¹)
  apply lp2_orbit_tendsto_of_compact_and_vanishing_eventual_mean_error μ W
    (electricalOrbitLp_compact_closure rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds)
    endpoint error errorConvergence
  intro block
  filter_upwards [eventually_ge_atTop (subsequence block+1)] with depth large
  have comparison := electricalOrbit_future_absolute_mean_le rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds endpoint endpointFixed membership (depth-(subsequence block+1)) (subsequence block)
  have depthEquality : depth-(subsequence block+1)+1+subsequence block = depth := by omega
  rwa [depthEquality] at comparison

include classical in
theorem exists_actual_electrical_L2_limit
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) ∧
      ∃ fixed : Lp ℝ 2 μ,
        normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth fixed = fixed ∧
        (∀ᵐ marks ∂μ, 0 < fixed marks) ∧ (∫ marks, fixed marks ∂μ) = 1 ∧
        ∃ amplitude : ℝ, 1 ≤ amplitude ∧
          Tendsto (electricalOrbitLp rule p positive belowOne fixedPoint growth) atTop (𝓝 (amplitude • fixed)) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, amplitude, amplitudeLower, membership, dominates, least⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (amplitude • fixed) = amplitude • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth amplitude
      (zero_le_one.trans amplitudeLower), fixedIdentity]
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, amplitude, amplitudeLower,
    electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth growthPositive
      growthBounds (amplitude • fixed) endpointFixed membership⟩

end
end IGSIII34.Percolation
