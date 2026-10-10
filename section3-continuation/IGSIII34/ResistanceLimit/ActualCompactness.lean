import IGSIII34.ResistanceLimit.ElectricalCompactness

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actualStationaryElectricalSpace_compact
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
        (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      markedElectricalRadius rule marks.val depth descendant state /
        growth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
    CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  unfold ActualStationaryElectricalSpace
  apply electricalSpace_compact_of_radius_bounds rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    marks.property.2.2 growth growthPositive _ marks.val (fun _ => rfl)
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  intro depth first last reachable
  exact actual_persistent_skeleton_resistances_tendsto rule marks.val marks.property.2.1 growth growthPositive
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fun address => (marks.property.1 address).le) fieldLimit depth reachable

/-- The actual electrical completion is compact almost surely. The hypotheses
are the already established natural growth bounds and actual omega endpoint;
no compactness, metric compatibility, or form is postulated. -/
theorem ae_actualStationaryElectricalSpace_compact_fixed_cluster
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ typical : StationaryElectricalTypical rule p positive belowOne fixedPoint growth endpoint marks,
        CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth endpoint
          (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩) := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have endpointPositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) endpoint membership
  filter_upwards [stationaryElectricalTypical_ae rule p positive belowOne fixedPoint growth endpoint
      growthPositive endpointPositive endpointFixed,
    actual_electrical_field_limits_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds endpoint endpointFixed membership,
    ae_uniform_actual_electrical_mesh_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
      constantPositive growthGreaterThanOne growthBounds endpoint endpointFixed membership eta etaPositive etaBelowOne
      productGreaterThanOne] with marks typical fieldLimit mesh
  obtain ⟨start, radiusBounds⟩ := mesh
  exact ⟨typical, actualStationaryElectricalSpace_compact rule p positive belowOne fixedPoint growth endpoint growthPositive
    ⟨marks, typical⟩ fieldLimit eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le) radiusBounds⟩

end
end IGSIII34.ResistanceLimit
