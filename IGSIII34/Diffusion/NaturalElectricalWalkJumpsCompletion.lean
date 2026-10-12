import IGSIII34.Diffusion.ElectricalHalfOwnershipCompletion
import IGSIII34.Diffusion.FiniteWalkEdgeJumpCompletion
import IGSIII34.Spectral.NaturalPhysicalCylinderMeshCompletion
import Universality.Percolation.ClassicalClusterNumber

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII34.Spectral IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actualElectrical_edge_jump_mesh_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (age : ℕ) (beyond : start ≤ age + 1)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    : ∀ (edge : ClusterEdge (rule.generation (0 + (age + 1))).network (stationaryConfiguration rule marks.val (0 + (age + 1)))),
    dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
        ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).1)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
        ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).2) ≤ 2 * coefficient * eta ^ (age + 1) := by
  intro edge
  have firstBound := actualElectrical_halfowner_mesh_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start radiusBound chemicalScale chemicalScalePositive 0 age beyond fallback edge true
  have lastBound := actualElectrical_halfowner_mesh_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start radiusBound chemicalScale chemicalScalePositive 0 age beyond fallback edge false
  change dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
    ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).1) _ ≤ coefficient * eta^(age + 1) at firstBound
  change dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
    ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).2) _ ≤ coefficient * eta^(age + 1) at lastBound
  have triangle := dist_triangle
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
      ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).1)
    (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age
      (actualComponentEdgeOwnership rule marks.val marks.property.2.1 0 (age + 1) fallback edge))
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (0 + (age + 1))
      ((clusterRetainedEndpoint (rule.generation (0 + (age + 1))).network _) edge).2)
  rw [dist_comm] at lastBound
  linarith

/-- The same actual physical natural endpoint supplies vanishing jump
sizes for every discrete neighbour trajectory and every finite initial law. -/
theorem ae_natural_electrical_walk_jumps_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreater : 1 < natural.growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ start : ℕ,
      ∀ (typical : StationaryElectricalTypical rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) marks),
      ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
      ∀ age : ℕ, start ≤ age + 1 →
      ∀ (initial : Measure (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive (age + 1)))
        (probability : IsProbabilityMeasure initial),
      letI := probability
      ∀ᵐ path ∂finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive (age + 1))
        (clusterRetainedEndpoint (rule.generation (age + 1)).network (stationaryConfiguration rule marks (age + 1)))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks typical.2.1 (age + 1) [] true)) initial,
      ∀ index, dist
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (age + 1) (path index))
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (age + 1) (path (index + 1))) ≤
        2 * ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(age + 1) := by
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  filter_upwards [ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      fixed membership eta etaPositive etaBelowOne productGreater,
    natural.almostSure, natural_physical_electrical_field_scaling_completion rule p positive belowOne fixedPoint natural]
      with marks mesh actualLimit scaling
  obtain ⟨start, radiusBound⟩ := mesh
  have fieldLimit : ∀ address, Tendsto (fun depth => natural.growth⁻¹^depth * electricalIteration rule marks depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks)) := by
    intro address
    rw [scaling address]
    exact actualLimit address
  refine ⟨start, ?_⟩
  intro typical chemicalScale chemicalScalePositive age beyond initial probability
  letI := probability
  have edgePositive : 0 < rule.edges := Nat.zero_lt_of_lt classicalRule.edges_gt_one
  let fallback : Fin (age + 1) → (Fin rule.edges × Bool) := fun _ => (⟨0, edgePositive⟩, true)
  exact finiteDiscreteWalkLaw_ae_edge_jump_completion _ _ initial
    (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
      (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ (age + 1) vertex)
    (2 * ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(age + 1))
    (by
      let boundedAt (depth : ℕ) : Prop := ∀ edge : ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth),
        dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ depth
            ((clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) edge).1)
          (actualStationaryElectricalVertex rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
            (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ depth
            ((clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks depth)) edge).2) ≤
              2 * ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(age + 1)
      have bound : boundedAt (0 + (age + 1)) :=
        actualElectrical_edge_jump_mesh_completion rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical⟩ fieldLimit eta
          ((rule.edges + 1 : ℝ) / (1 - eta)) start radiusBound chemicalScale chemicalScalePositive age beyond fallback
      rw [Nat.zero_add] at bound
      exact bound)

theorem natural_electrical_jump_rate_tendsto_zero_completion
    (rule : Rule) (eta : ℝ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1) :
    Tendsto (fun age : ℕ => 2 * ((rule.edges + 1 : ℝ) / (1 - eta)) * eta^(age + 1)) atTop (𝓝 0) := by
  have converges := (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, mul_zero] using converges.const_mul (2 * ((rule.edges + 1 : ℝ) / (1 - eta)))

end
end IGSIII34.Diffusion

