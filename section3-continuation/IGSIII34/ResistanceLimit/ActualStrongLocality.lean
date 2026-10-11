import IGSIII34.ResistanceLimit.ActualTraceMesh
import IGSIII34.ResistanceLimit.CompletionLocality

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

/-- Strong locality is stated on the unique continuous-extension domain of the
actual full retained electrical completion. -/
def ActualCompletionStrongLocality : Prop :=
  ∀ first second : energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks),
    ∀ neighborhood : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)),
      IsOpen neighborhood →
      IsCompact (closure (Function.support
        (completionExtension
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
          (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) second))) →
      closure (Function.support
        (completionExtension
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
          (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) second)) ⊆ neighborhood →
      (∀ firstPoint ∈ neighborhood, ∀ lastPoint ∈ neighborhood,
        completionExtension
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
          (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) first firstPoint =
        completionExtension
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
          (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) first lastPoint) →
      limitingPairing
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) first.val second.val = 0

theorem actual_completion_strongly_local_of_mesh
    (mesh : ℕ → ℝ) (meshZero : Tendsto mesh atTop (𝓝 0))
    (edgeBound : ∀ depth edge,
      actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth edge ≠ 0 →
      dist (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth edge).1
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth edge).2 ≤ mesh depth) :
    ActualCompletionStrongLocality rule p positive belowOne fixedPoint growth value growthPositive marks := by
  intro first second neighborhood openNeighborhood supportCompact supportSubset constant
  exact completionExtension_strongly_local
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    mesh meshZero edgeBound first second neighborhood openNeighborhood supportCompact supportSubset constant

theorem ae_actual_completion_strongly_local_fixed_cluster
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
        ActualCompletionStrongLocality rule p positive belowOne fixedPoint growth value
          (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ := by
  filter_upwards [ae_actual_trace_endpoint_mesh_fixed_cluster rule p positive belowOne fixedPoint growth value
    classicalRule constant constantPositive growthGreaterThanOne growthBounds fixed membership
    eta etaPositive etaBelowOne productGreaterThanOne] with marks mesh
  obtain ⟨typical, mesh, meshZero, edgeBound⟩ := mesh
  exact ⟨typical, actual_completion_strongly_local_of_mesh rule p positive belowOne fixedPoint growth value
    (zero_lt_one.trans growthGreaterThanOne) ⟨marks, typical⟩ mesh meshZero edgeBound⟩

end
end IGSIII34.ResistanceLimit
