import IGSIII34.Diffusion.ActualFiniteTraceConvergenceCompletion20261011
import IGSIII34.ResistanceLimit.GenerationBlockEnergyCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open Resistance Resistance.FiniteNetwork
open scoped BigOperators _root_.Topology

theorem coarseResistance_constant_scale_completion20261011
    {outerEdges innerVertices innerEdges : ℕ}
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (edge : {edge : Fin outerEdges // inner.coarseConfiguration configuration edge = true}) :
    coarseResistance inner configuration (fun _ => scalar) edge =
      scalar * unitConfigurationResistance inner (configuration edge.val) := by
  have connected := connected_of_crosses inner (configuration edge.val) edge.property
  have scaling := (network inner (configuration edge.val)).effectiveResistance_scale
    ((network inner (configuration edge.val)).unitFlows_nonempty_of_connected connected)
    (resistance := fun _ => 1) (scalar := scalar) (fun _ => zero_le_one) scalarNonnegative
  simpa only [coarseResistance, unitConfigurationResistance, electricalCell, mul_one] using scaling

/-- Every prescribed old-vertex potential has an exact energy-minimising
extension in the true microscopic generation. Its trace retains the
entire source component and every hanging edge. -/
theorem exists_original_generation_trace_minimizer_completion20261011
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (scalar : ℝ) (scalarPositive : 0 < scalar)
    (boundary : Fin (rule.generation coarse).vertices → ℝ) :
    ∃ potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ,
      (∀ vertex, (network (rule.generation coarse).network
        ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration))).graph.Reachable
          (rule.generation coarse).network.source vertex →
        potential (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration)
        (fun _ => scalar) potential =
      sourceComponentEnergy (network (rule.generation coarse).network
        ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration)))
        (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration edge.val)) boundary := by
  let cells := generationBlockCells rule coarse fine configuration
  obtain ⟨potential, restriction, minimizing⟩ := exists_actual_sourceComponentEnergy_minimizer
    (rule.generation coarse).network (rule.generation fine).network cells
    (fun _ => scalar) (fun _ => scalarPositive) boundary
  refine ⟨fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex vertex), ?_, ?_⟩
  · intro vertex retained
    have equality := restriction vertex retained
    simpa only [blockOldVertexEmbedding, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] using equality
  have transport := sourceComponentEnergy_network_equivalence (rule.generationBlockDecomposition coarse fine)
    configuration (fun _ => scalar) potential
  have configurationIdentity :
      (rule.generationBlockDecomposition coarse fine).configuration configuration =
        substitutionConfigurationEquiv cells := by
    simp [cells, generationBlockCells, generationBlockCellsEquiv]
  rw [configurationIdentity] at transport
  have resistanceIdentity : coarseResistance (rule.generation fine).network cells (fun _ => scalar) =
      fun edge => scalar * unitConfigurationResistance (rule.generation fine).network (cells edge.val) := by
    funext edge
    exact coarseResistance_constant_scale_completion20261011 _ _ scalar scalarPositive.le edge
  rw [resistanceIdentity] at minimizing
  exact transport.symm.trans minimizing

theorem original_generation_trace_energy_le_completion20261011
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (scalar : ℝ) (scalarPositive : 0 < scalar)
    (potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) :
    sourceComponentEnergy (network (rule.generation coarse).network
      ((rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine configuration)))
      (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine configuration edge.val))
      (fun vertex => potential (blockOldVertexEmbedding rule coarse fine vertex)) ≤
    sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network configuration)
      (fun _ => scalar) potential := by
  let cells := generationBlockCells rule coarse fine configuration
  have comparison := sourceComponentEnergy_le_actual_substitution_energy (rule.generation coarse).network
    (rule.generation fine).network cells (fun _ => scalar) (fun _ => scalarPositive)
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm vertex))
  have transport := sourceComponentEnergy_network_equivalence (rule.generationBlockDecomposition coarse fine)
    configuration (fun _ => scalar)
    (fun vertex => potential ((rule.generationBlockDecomposition coarse fine).vertex.symm vertex))
  simp only [Equiv.symm_apply_apply] at transport
  have configurationIdentity :
      (rule.generationBlockDecomposition coarse fine).configuration configuration =
        substitutionConfigurationEquiv cells := by
    simp [cells, generationBlockCells, generationBlockCellsEquiv]
  rw [configurationIdentity] at transport
  rw [transport] at comparison
  have resistanceIdentity : coarseResistance (rule.generation fine).network cells (fun _ => scalar) =
      fun edge => scalar * unitConfigurationResistance (rule.generation fine).network (cells edge.val) := by
    funext edge
    exact coarseResistance_constant_scale_completion20261011 _ _ scalar scalarPositive.le edge
  rw [resistanceIdentity] at comparison
  exact comparison

/-- A bound on the true microscopic energies passes to every fixed
stationary trace whenever the persistent old values converge. This is
the actual fixed-trace lower semicontinuity step. -/
theorem actual_original_energy_bound_passes_to_trace_completion20261011
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldPositive : ∀ address, 0 < field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ)
    (limitPotential : Fin (rule.generation coarse).vertices → ℝ)
    (oldValuesConverge : ∀ vertex, Tendsto
      (fun fine => potentials fine (blockOldVertexEmbedding rule coarse fine vertex)) atTop (𝓝 (limitPotential vertex)))
    (bound : ℝ)
    (energyBound : ∀ fine, sourceComponentEnergy
      (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
      (fun _ => (growth ^ (coarse + fine + 2))⁻¹) (potentials fine) ≤ bound) :
    sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
      (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) limitPotential ≤ bound := by
  have traceConverges := finiteSourceEnergy_tendsto_completion20261011
    (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
    (fun fine edge => (growth ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance
      (rule.generation fine).network
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val))
    (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val)
    (fun edge => actual_marked_block_resistance_limit rule marks crossing growth field fieldLimit coarse edge)
    (fun edge => ne_of_gt (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)))
    (fun fine vertex => potentials fine (blockOldVertexEmbedding rule coarse fine vertex)) limitPotential oldValuesConverge
  apply le_of_tendsto traceConverges
  apply Eventually.of_forall
  intro fine
  have comparison := original_generation_trace_energy_le_completion20261011 rule coarse fine
    (stationaryConfiguration rule marks (coarse + fine + 1))
    ((growth ^ (coarse + fine + 2))⁻¹) (inv_pos.mpr (pow_pos growthPositive _)) (potentials fine)
  have coarseIdentity := generationBlockCoarse_of_coherent rule (stationaryConfiguration rule marks)
    (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth [] true) coarse fine
  change (rule.generation fine).network.coarseConfiguration
    (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1))) =
      stationaryConfiguration rule marks coarse at coarseIdentity
  rw [coarseIdentity] at comparison
  exact comparison.trans (energyBound fine)

end
end IGSIII34.Diffusion
