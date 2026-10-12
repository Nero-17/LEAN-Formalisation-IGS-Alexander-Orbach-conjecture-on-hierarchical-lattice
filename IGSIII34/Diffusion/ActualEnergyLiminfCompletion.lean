import IGSIII34.Diffusion.ActualGlobalEnergyLowerCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- The sharp original-to-stationary energy lower bound uses the actual
converging microscopic energies; no uniform bound by their exact limit is
required. -/
theorem actual_original_energy_limit_passes_to_trace_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldPositive : ∀ address, 0 < field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ)
    (limitPotential : Fin (rule.generation coarse).vertices → ℝ)
    (oldValuesConverge : ∀ vertex, Tendsto
      (fun fine => potentials fine (blockOldVertexEmbedding rule coarse fine vertex)) atTop (𝓝 (limitPotential vertex)))
    (limitEnergy : ℝ)
    (energiesConverge : Tendsto (fun fine => sourceComponentEnergy
      (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
      (fun _ => (growth ^ (coarse + fine + 2))⁻¹) (potentials fine)) atTop (𝓝 limitEnergy)) :
    sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
      (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) limitPotential ≤ limitEnergy := by
  have traceConverges := finiteSourceEnergy_tendsto_completion
    (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
    (fun fine edge => (growth ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance
      (rule.generation fine).network
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val))
    (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val)
    (fun edge => actual_marked_block_resistance_limit rule marks crossing growth field fieldLimit coarse edge)
    (fun edge => ne_of_gt (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)))
    (fun fine vertex => potentials fine (blockOldVertexEmbedding rule coarse fine vertex)) limitPotential oldValuesConverge
  apply le_of_tendsto_of_tendsto traceConverges energiesConverge
  apply Eventually.of_forall
  intro fine
  have comparison := original_generation_trace_energy_le_completion rule coarse fine
    (stationaryConfiguration rule marks (coarse + fine + 1))
    ((growth ^ (coarse + fine + 2))⁻¹) (inv_pos.mpr (pow_pos growthPositive _)) (potentials fine)
  have coarseIdentity := generationBlockCoarse_of_coherent rule (stationaryConfiguration rule marks)
    (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth [] true) coarse fine
  change (rule.generation fine).network.coarseConfiguration
    (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1))) =
      stationaryConfiguration rule marks coarse at coarseIdentity
  rw [coarseIdentity] at comparison
  exact comparison

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualOriginalPotential_sharp_energy_lower_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (limitPotential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ)
    (oldValuesConverge : ∀ coarse vertex, Tendsto
      (fun fine => potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex)) atTop
      (𝓝 (limitPotential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))))
    (limitEnergy : ℝ)
    (energiesConverge : Tendsto (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop (𝓝 limitEnergy)) :
    limitPotential ∈ energyDomain
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) ∧
    limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) limitPotential ≤ limitEnergy := by
  have traceBound (coarse : ℕ) : traceEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) coarse limitPotential ≤ limitEnergy := by
    rw [actualEnergy_trace_eq_source_completion]
    apply actual_original_energy_limit_passes_to_trace_completion rule marks.val marks.property.1.2.1
      growth growthPositive (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
      marks.property.1.1 fieldLimit coarse (fun fine => potentials (coarse + fine + 1))
      (fun vertex => limitPotential (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse vertex))
      (oldValuesConverge coarse) limitEnergy
    have shifted := energiesConverge.comp (tendsto_add_atTop_nat (coarse + 1))
    apply shifted.congr' (Eventually.of_forall fun fine => ?_)
    simp only [Function.comp_def]
    have depthIdentity : fine + (coarse + 1) = coarse + fine + 1 := by omega
    rw [depthIdentity]
  exact ⟨⟨limitEnergy, by rintro _ ⟨coarse, rfl⟩; exact traceBound coarse⟩, ciSup_le traceBound⟩

end
end IGSIII34.Diffusion
