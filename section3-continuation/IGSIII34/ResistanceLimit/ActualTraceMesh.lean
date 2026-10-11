import IGSIII34.ResistanceLimit.ActualSkeletonEnergy
import IGSIII34.ResistanceLimit.SkeletonEdgeMesh
import IGSIII34.Forms.StationaryWeightMesh

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

def actualTraceMesh (eta : ℝ) (threshold depth : ℕ) : ℝ :=
  if threshold ≤ depth + 1 then eta ^ (depth + 1)
  else ∑ edge, stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth edge

theorem actualTraceMesh_tendsto (eta : ℝ) (threshold : ℕ)
    (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1) :
    Tendsto (actualTraceMesh rule p positive belowOne fixedPoint growth value marks eta threshold) atTop (𝓝 0) := by
  have powerConvergence : Tendsto (fun depth : ℕ => eta ^ (depth + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)
  apply powerConvergence.congr'
  filter_upwards [eventually_ge_atTop threshold] with depth beyond
  simp only [actualTraceMesh, if_pos (show threshold ≤ depth + 1 by omega)]

theorem actual_trace_endpoint_mesh (eta : ℝ) (threshold : ℕ)
    (weights : ∀ depth, threshold ≤ depth + 1 → ∀ edge,
      stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth edge ≤ eta ^ (depth + 1)) :
    ∀ depth edge, actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth edge ≠ 0 →
      dist (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth edge).1
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth edge).2 ≤
      actualTraceMesh rule p positive belowOne fixedPoint growth value marks eta threshold depth := by
  intro depth edge nonzero
  have bound := skeletonEnergyEndpoint_distance_le_resistance rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 depth edge nonzero
  refine bound.trans ?_
  unfold actualTraceMesh
  split_ifs with beyond
  · exact weights depth beyond edge
  · exact Finset.single_le_sum (fun other _ =>
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth other).le)
      (Finset.mem_univ edge)

theorem ae_actual_trace_endpoint_mesh_fixed_cluster
    (classicalRule : rule.Classical) (constant : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (membership : value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ typical : StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks,
        ∃ mesh : ℕ → ℝ, Tendsto mesh atTop (𝓝 0) ∧
          ∀ depth edge,
            actualEnergyConductance rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩ depth edge ≠ 0 →
            dist (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value
                (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ depth edge).1
              (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value
                (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ depth edge).2 ≤ mesh depth := by
  have endpointPositive := electricalOmega_ae_positive rule classicalRule p positive belowOne fixedPoint growth
    (zero_lt_one.trans growthGreaterThanOne) (fun depth => (growthBounds depth).1) value membership
  filter_upwards [stationaryEnergyTypical_ae rule p positive belowOne fixedPoint growth value
      (zero_lt_one.trans growthGreaterThanOne) endpointPositive fixed,
    ae_stationary_generation_weight_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint constant growth
      constantPositive growthGreaterThanOne growthBounds value fixed membership eta etaPositive etaBelowOne productGreaterThanOne]
    with marks typical weights
  obtain ⟨threshold, weights⟩ := weights
  refine ⟨typical, actualTraceMesh rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩ eta threshold,
    actualTraceMesh_tendsto rule p positive belowOne fixedPoint growth value ⟨marks, typical⟩ eta threshold etaPositive.le etaBelowOne, ?_⟩
  apply actual_trace_endpoint_mesh rule p positive belowOne fixedPoint growth value
    (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ eta threshold
  intro depth beyond edge
  exact weights depth beyond edge.val

end
end IGSIII34.ResistanceLimit
