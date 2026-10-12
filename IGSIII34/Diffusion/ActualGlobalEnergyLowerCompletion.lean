import IGSIII34.Diffusion.ActualFixedTraceRecoveryCompletion
import IGSIII34.ResistanceLimit.ActualSkeletonEnergy

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

def actualEnergyFiniteVertexCompletion (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks :=
  electricalSkeletonPoint rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 depth vertex

theorem actualEnergy_trace_eq_source_completion (depth : ℕ)
    (potential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ) :
    traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth potential =
    sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val depth)
      (fun vertex => potential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) :=
  skeleton_traceEnergy_eq_source_energy rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    marks.property.1.2.2 depth potential

/-- Uniformly bounded real microscopic energies and convergence on every
persistent old vertex give membership in the actual limiting energy
domain and the full limiting-energy lower bound. -/
theorem actualOriginalPotential_limit_energy_bound_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (limitPotential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (oldValuesConverge : ∀ coarse vertex, Tendsto
      (fun fine => potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex)) atTop
      (𝓝 (limitPotential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))))
    (bound : ℝ)
    (energyBound : ∀ depth, sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth) ≤ bound) :
    limitPotential ∈ energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) ∧
    limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) limitPotential ≤ bound := by
  have traceBound (coarse : ℕ) : traceEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) coarse limitPotential ≤ bound := by
    rw [actualEnergy_trace_eq_source_completion]
    exact actual_original_energy_bound_passes_to_trace_completion rule marks.val marks.property.1.2.1
      growth growthPositive (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
      marks.property.1.1 fieldLimit coarse (fun fine => potentials (coarse + fine + 1))
      (fun vertex => limitPotential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))
      (oldValuesConverge coarse) bound (fun fine => by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using energyBound (coarse + fine + 1))
  constructor
  · exact ⟨bound, by rintro _ ⟨coarse, rfl⟩; exact traceBound coarse⟩
  · exact ciSup_le traceBound

end
end IGSIII34.Diffusion
