import IGSIII34.Diffusion.NaturalElectricalWalkJumpsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actualElectrical_walk_eventually_small_jumps_completion20261011
    (rule : Rule) (edgePositive : 0 < rule.edges) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ᵐ path ∂finiteDiscreteWalkLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)) (initial depth),
      ∀ index, dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth (path index))
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth (path (index + 1))) ≤ tolerance := by
  have rate : Tendsto (fun depth : ℕ => 2 * coefficient * eta ^ depth) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).const_mul (2 * coefficient)
  filter_upwards [rate.eventually (eventually_lt_nhds tolerancePositive), eventually_ge_atTop start,
    eventually_ge_atTop 1] with depth small beyond nonzero
  cases depth with
  | zero => omega
  | succ age =>
    let fallback : Fin (age + 1) → Fin rule.edges × Bool := fun _ => (⟨0, edgePositive⟩, true)
    let boundedAt (depth : ℕ) : Prop := ∀ edge : ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth),
      dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth
        ((clusterRetainedEndpoint (rule.generation depth).network _) edge).1)
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth
        ((clusterRetainedEndpoint (rule.generation depth).network _) edge).2) ≤ 2 * coefficient * eta ^ (age + 1)
    have bound : boundedAt (0 + (age + 1)) := actualElectrical_edge_jump_mesh_completion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks fieldLimit eta coefficient start radiusBound chemicalScale chemicalScalePositive age beyond fallback
    rw [Nat.zero_add] at bound
    exact finiteDiscreteWalkLaw_ae_edge_jump_completion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (age + 1))
      (clusterRetainedEndpoint (rule.generation (age + 1)).network (stationaryConfiguration rule marks.val (age + 1)))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 (age + 1) [] true))
      (initial (age + 1))
      (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (age + 1) vertex) tolerance
      (fun edge => (bound edge).trans small.le)

end
end IGSIII34.Diffusion
