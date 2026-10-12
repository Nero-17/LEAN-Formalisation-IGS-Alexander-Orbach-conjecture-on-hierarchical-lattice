import IGSIII34.Diffusion.BoundedSkeletonSubsequenceCompletion
import IGSIII34.ResistanceLimit.HarmonicTower

set_option autoImplicit false
set_option maxHeartbeats 4000000
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

/-- The sharp actual energy bound remains valid on an arbitrary diverging
subsequence. Old-vertex consistency is required only on the retained
cluster, so no fictitious boundary values are imposed outside it. -/
theorem actualOriginal_subsequence_energy_lower_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (functions : ℕ → ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (oldConsistent : ∀ coarse fine vertex,
      ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks.val coarse)).Reachable
        (rule.generation coarse).network.source vertex →
      functions (coarse + fine + 1) (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex) =
      potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex))
    (selected : ℕ → ℕ) (selectedDiverges : Tendsto selected atTop atTop)
    (limitPotential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (pointwiseConverges : ∀ point, Tendsto (fun index => functions (selected index) point) atTop (𝓝 (limitPotential point)))
    (limitEnergy : ℝ)
    (energyConverges : Tendsto (fun index => sourceComponentEnergy
      (network (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)))
      (fun _ => (growth ^ (selected index + 1))⁻¹) (potentials (selected index))) atTop (𝓝 limitEnergy)) :
    limitPotential ∈ energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) ∧
    limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) limitPotential ≤ limitEnergy := by
  classical
  have traceBound (coarse : ℕ) : traceEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) coarse limitPotential ≤ limitEnergy := by
    rw [actualEnergy_trace_eq_source_completion]
    let fineDepth (index : ℕ) := selected index - coarse - 1
    have fineDiverges : Tendsto fineDepth atTop atTop := by
      apply tendsto_atTop.mpr
      intro minimum
      filter_upwards [selectedDiverges.eventually (eventually_ge_atTop (minimum + coarse + 1))] with index large
      dsimp [fineDepth]
      omega
    let response (index : ℕ) (edge : {edge : Fin (rule.generation coarse).edges // stationaryConfiguration rule marks.val coarse edge = true}) :=
      (growth ^ (coarse + fineDepth index + 2))⁻¹ * unitConfigurationResistance (rule.generation (fineDepth index)).network
        (generationBlockCells rule coarse (fineDepth index) (stationaryConfiguration rule marks.val (coarse + fineDepth index + 1)) edge.val)
    have responseConverges (edge : {edge : Fin (rule.generation coarse).edges // stationaryConfiguration rule marks.val coarse edge = true}) :
        Tendsto (fun index => response index edge) atTop
        (𝓝 (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse edge)) :=
      (actual_marked_block_resistance_limit rule marks.val marks.property.1.2.1 growth
        (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) fieldLimit coarse edge).comp fineDiverges
    have traceConverges := finiteSourceEnergy_tendsto_completion
      (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) response
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) responseConverges
      (fun edge => (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks) coarse edge).ne')
      (fun index vertex => functions (selected index) (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))
      (fun vertex => limitPotential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))
      (fun vertex => pointwiseConverges _)
    apply le_of_tendsto_of_tendsto traceConverges energyConverges
    filter_upwards [selectedDiverges.eventually (eventually_ge_atTop (coarse + 1))] with index large
    have depthIdentity : selected index = coarse + fineDepth index + 1 := by dsimp [fineDepth]; omega
    have comparison := original_generation_trace_energy_le_completion rule coarse (fineDepth index)
      (stationaryConfiguration rule marks.val (coarse + fineDepth index + 1))
      ((growth ^ (coarse + fineDepth index + 2))⁻¹) (inv_pos.mpr (pow_pos growthPositive _))
      (potentials (coarse + fineDepth index + 1))
    have coarseIdentity := generationBlockCoarse_of_coherent rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
        (energyTypicalElectricalMarks rule p positive belowOne fixedPoint growth value marks)) coarse (fineDepth index)
    change (rule.generation (fineDepth index)).network.coarseConfiguration
      (generationBlockCells rule coarse (fineDepth index)
        (stationaryConfiguration rule marks.val (coarse + fineDepth index + 1))) = stationaryConfiguration rule marks.val coarse at coarseIdentity
    rw [coarseIdentity] at comparison
    have oldEquality := sourceComponentEnergy_congr_retained
      (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) (response index)
      (fun vertex => functions (selected index) (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))
      (fun vertex => potentials (coarse + fineDepth index + 1) (blockOldVertexEmbedding rule coarse (fineDepth index) vertex)) (by
        intro vertex retained
        rw [graph_eq_openGraph] at retained
        rw [depthIdentity]
        exact oldConsistent coarse (fineDepth index) vertex retained)
    rw [oldEquality]
    rw [depthIdentity]
    exact comparison
  exact ⟨⟨limitEnergy, by rintro _ ⟨coarse, rfl⟩; exact traceBound coarse⟩, ciSup_le traceBound⟩

end
end IGSIII34.Diffusion
