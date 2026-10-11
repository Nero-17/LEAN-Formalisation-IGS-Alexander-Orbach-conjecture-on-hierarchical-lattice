import IGSIII34.Diffusion.OriginalGenerationTraceRecoveryCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open Resistance Resistance.FiniteNetwork
open scoped BigOperators _root_.Topology

/-- The microscopic recovery potentials are selected from proved exact
minimisers, and their real normalised unit-edge energies converge to the
fixed stationary trace energy. Uniform convergence of these functions on
the complete carrier is a separate obligation. -/
theorem exists_actual_fixed_trace_recovery_completion20261011
    (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldPositive : ∀ address, 0 < field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) :
    ∃ potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ,
      (∀ fine vertex, (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse)).graph.Reachable
        (rule.generation coarse).network.source vertex →
        potentials fine (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      Tendsto (fun fine => sourceComponentEnergy
        (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
        (fun _ => (growth ^ (coarse + fine + 2))⁻¹) (potentials fine)) atTop
        (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
          (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) boundary)) := by
  have recoveryExists (fine : ℕ) :
      ∃ potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ,
        (∀ vertex, (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse)).graph.Reachable
          (rule.generation coarse).network.source vertex →
          potential (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
        sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network
          (stationaryConfiguration rule marks (coarse + fine + 1))) (fun _ => (growth ^ (coarse + fine + 2))⁻¹) potential =
        sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
          (fun edge => (growth ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance (rule.generation fine).network
            (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val)) boundary := by
    have minimizing := exists_original_generation_trace_minimizer_completion20261011 rule coarse fine
      (stationaryConfiguration rule marks (coarse + fine + 1))
      ((growth ^ (coarse + fine + 2))⁻¹) (inv_pos.mpr (pow_pos growthPositive _)) boundary
    have coarseIdentity := generationBlockCoarse_of_coherent rule (stationaryConfiguration rule marks)
      (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth [] true) coarse fine
    change (rule.generation fine).network.coarseConfiguration
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1))) =
        stationaryConfiguration rule marks coarse at coarseIdentity
    rw [coarseIdentity] at minimizing
    exact minimizing
  choose potentials restriction minimizing using recoveryExists
  refine ⟨potentials, restriction, ?_⟩
  have traceConverges := actual_fixed_coarse_trace_energy_tendsto_completion20261011 rule marks crossing
    growth growthPositive field fieldPositive fieldLimit coarse boundary
  exact traceConverges.congr' (Eventually.of_forall fun fine => (minimizing fine).symm)

end
end IGSIII34.Diffusion
