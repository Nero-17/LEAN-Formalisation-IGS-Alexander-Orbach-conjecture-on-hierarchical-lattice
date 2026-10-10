import IGSIII34.Percolation.ElectricalConditionalFuture
import IGSIII34.Percolation.ElectricalGeometricResidual
import IGSIII34.Percolation.ElectricalL2Convergence
import IGSIII34.Probability.ConditionalPositivePart
import IGSIII34.Probability.ConditionalShiftedConvergence

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth
local notation "F" => coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbitLp_tendsto_ae_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∀ᵐ marks ∂μ, Tendsto (fun depth => W depth marks) atTop (𝓝 (endpoint marks)) := by
  have convergence := electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds endpoint endpointFixed membership
  obtain ⟨bound, rate, boundNonnegative, rateNonnegative, rateBelowOne, estimates⟩ :=
    exists_electricalOrbit_geometric_prefix_residual rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds
  have endpointResidual := electrical_limit_geometric_prefix_residual rule p positive belowOne fixedPoint
    growth bound rate estimates endpoint convergence
  obtain ⟨subsequence, increasing, subsequenceConvergence, forward, backward⟩ :=
    exists_electrical_endpoint_comparison_subsequence rule classical p positive belowOne fixedPoint
      growth growthPositive (fun depth => (growthBounds depth).1) endpoint membership
  change Tendsto (fun depth => electricalComparisonCoefficient μ (W (subsequence depth)) endpoint) atTop (𝓝 0) at forward
  change Tendsto (fun depth => electricalComparisonCoefficient μ endpoint (W (subsequence depth))) atTop (𝓝 0) at backward
  have centered (block : ℕ) (blockPositive : 1 ≤ block) :
      (∀ᵐ marks ∂μ, Tendsto (fun depth => max (W (depth+1+block) marks-endpoint marks) 0-
        μ[fun marks => max (W (depth+1+block) marks-endpoint marks) 0 | F (depth+1)] marks) atTop (𝓝 0)) ∧
      (∀ᵐ marks ∂μ, Tendsto (fun depth => max (endpoint marks-W (depth+1+block) marks) 0-
        μ[fun marks => max (endpoint marks-W (depth+1+block) marks) 0 | F (depth+1)] marks) atTop (𝓝 0)) := by
    have orbitResidual (depth : ℕ) : ‖W (depth+1+block)-electricalPrefixProjection rule p positive belowOne fixedPoint depth
        (W (depth+1+block))‖ ≤ bound*rate^depth := by
      have indexEquality : depth+(block-1)+2 = depth+1+block := by omega
      simpa only [indexEquality] using estimates depth (block-1)
    exact ⟨ae_positive_part_sub_condExp_tendsto_zero μ (fun depth => F (depth+1)) (fun depth => (F).le (depth+1))
      (fun depth => W (depth+1+block)) (fun _ => endpoint) bound bound rate boundNonnegative boundNonnegative rateNonnegative rateBelowOne
      orbitResidual endpointResidual,
      ae_positive_part_sub_condExp_tendsto_zero μ (fun depth => F (depth+1)) (fun depth => (F).le (depth+1))
      (fun _ => endpoint) (fun depth => W (depth+1+block)) bound bound rate boundNonnegative boundNonnegative rateNonnegative rateBelowOne
      endpointResidual orbitResidual⟩
  apply ae_tendsto_of_shifted_conditional_comparisons μ (fun depth => F (depth+1))
    (fun depth marks => W depth marks) endpoint (fun index => subsequence (index+1)+1)
    (fun index => electricalComparisonCoefficient μ (W (subsequence (index+1))) endpoint)
    (fun index => electricalComparisonCoefficient μ endpoint (W (subsequence (index+1))))
    (forward.comp (tendsto_add_atTop_nat 1)) (backward.comp (tendsto_add_atTop_nat 1))
    (fun marks => endpoint marks+1)
    (fun marks => constant⁻¹*((∫ marks, (endpoint marks)⁻¹ ∂μ)*endpoint marks+1))
  · intro index
    simpa only [Nat.add_assoc, Nat.add_comm 1 (subsequence (index+1))] using
      (electricalOrbit_future_conditional_bounds rule classical p positive belowOne fixedPoint
        constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership (subsequence (index+1))).1
  · intro index
    simpa only [Nat.add_assoc, Nat.add_comm 1 (subsequence (index+1))] using
      (electricalOrbit_future_conditional_bounds rule classical p positive belowOne fixedPoint
        constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership (subsequence (index+1))).2
  · intro index
    have blockPositive : 1 ≤ subsequence (index+1) := (by omega : 1 ≤ index+1).trans (increasing.id_le (index+1))
    simpa only [Nat.add_assoc, Nat.add_comm 1 (subsequence (index+1))] using (centered (subsequence (index+1)) blockPositive).1
  · intro index
    have blockPositive : 1 ≤ subsequence (index+1) := (by omega : 1 ≤ index+1).trans (increasing.id_le (index+1))
    simpa only [Nat.add_assoc, Nat.add_comm 1 (subsequence (index+1))] using (centered (subsequence (index+1)) blockPositive).2

end
end IGSIII34.Percolation

