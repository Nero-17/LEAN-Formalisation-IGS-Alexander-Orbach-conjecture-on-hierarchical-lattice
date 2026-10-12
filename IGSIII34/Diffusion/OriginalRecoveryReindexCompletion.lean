import IGSIII34.ResistanceLimit.OriginalBoundedTraceMinimizerCompletion
import IGSIII34.Diffusion.ActualFixedTraceRecoveryCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

def originalRecoveryGlobalPotentialCompletion (rule : Rule) (coarse : ℕ)
    (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) (fallback : ℝ)
    (depth : ℕ) : Fin (rule.generation depth).vertices → ℝ :=
  if after : coarse + 1 ≤ depth then
    fun vertex => potentials (depth - coarse - 1) (Fin.cast
      (congrArg (fun level => (rule.generation level).vertices) (by omega : depth = coarse + (depth - coarse - 1) + 1)) vertex)
  else fun _ => fallback

theorem originalRecoveryFamily_cast_level_completion
    (rule : Rule) (coarse : ℕ) (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ)
    (first second : ℕ) (equal : first = second) (vertex : Fin (rule.generation (coarse + second + 1)).vertices) :
    potentials first (Fin.cast (congrArg (fun fine => (rule.generation (coarse + fine + 1)).vertices) equal.symm) vertex) =
      potentials second vertex := by
  cases equal
  rfl

theorem originalRecoveryGlobalPotential_level_completion
    (rule : Rule) (coarse : ℕ)
    (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ) (fallback : ℝ) (fine : ℕ) :
    originalRecoveryGlobalPotentialCompletion rule coarse potentials fallback (coarse + fine + 1) = potentials fine := by
  unfold originalRecoveryGlobalPotentialCompletion
  rw [dif_pos (by omega : coarse + 1 ≤ coarse + fine + 1)]
  have fineIdentity : coarse + fine + 1 - coarse - 1 = fine := by omega
  funext vertex
  exact originalRecoveryFamily_cast_level_completion rule coarse potentials _ fine fineIdentity vertex

theorem originalRecoveryGlobalPotential_bounded_completion
    (rule : Rule) (coarse : ℕ)
    (potentials : ∀ fine, Fin (rule.generation (coarse + fine + 1)).vertices → ℝ)
    (fallback bound : ℝ) (fallbackBound : |fallback| ≤ bound) (bounded : ∀ fine vertex, |potentials fine vertex| ≤ bound) :
    ∀ depth vertex, |originalRecoveryGlobalPotentialCompletion rule coarse potentials fallback depth vertex| ≤ bound := by
  intro depth vertex
  unfold originalRecoveryGlobalPotentialCompletion
  split_ifs
  · exact bounded _ _
  · exact fallbackBound

/-- Bounded real original minimizers form a whole-generation recovery
family with the correct exact normalized energy limit. The level shift is
proved by an explicit cast, including the finitely many initial levels. -/
theorem exists_actual_bounded_global_trace_recovery_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldPositive : ∀ address, 0 < field address)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address) atTop (𝓝 (field address)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (boundaryBound : ∀ vertex, (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse)).graph.Reachable
      (rule.generation coarse).network.source vertex → |boundary vertex| ≤ bound) :
    ∃ potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ,
      (∀ depth vertex, |potentials depth vertex| ≤ bound) ∧
      (∀ fine vertex, (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse)).graph.Reachable
        (rule.generation coarse).network.source vertex →
        potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      Tendsto (fun depth => sourceComponentEnergy
        (network (rule.generation depth).network (stationaryConfiguration rule marks depth))
        (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop
        (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
          (fun edge => stationaryGenerationResistance rule field growth coarse [] edge.val) boundary)) := by
  have recoveryExists (fine : ℕ) := exists_original_generation_bounded_trace_minimizer_completion rule coarse fine
    (stationaryConfiguration rule marks (coarse + fine + 1)) ((growth ^ (coarse + fine + 2))⁻¹)
    (inv_pos.mpr (pow_pos growthPositive _)) boundary bound boundNonnegative
  have coarseIdentity (fine : ℕ) : (rule.generation fine).network.coarseConfiguration
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1))) =
        stationaryConfiguration rule marks coarse :=
    generationBlockCoarse_of_coherent rule (stationaryConfiguration rule marks)
      (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth [] true) coarse fine
  have chosenExists (fine : ℕ) : ∃ potential : Fin (rule.generation (coarse + fine + 1)).vertices → ℝ,
      (∀ vertex, |potential vertex| ≤ bound) ∧
      (∀ vertex, (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse)).graph.Reachable
        (rule.generation coarse).network.source vertex → potential (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks (coarse + fine + 1)))
        (fun _ => (growth ^ (coarse + fine + 2))⁻¹) potential =
      sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks coarse))
        (fun edge => (growth ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance (rule.generation fine).network
          (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1)) edge.val)) boundary := by
    have witness := recoveryExists fine
    rw [coarseIdentity fine] at witness
    exact witness boundaryBound
  choose finePotentials bounded restriction minimizing using chosenExists
  let potentials := originalRecoveryGlobalPotentialCompletion rule coarse finePotentials (boundary (rule.generation coarse).network.source)
  refine ⟨potentials, originalRecoveryGlobalPotential_bounded_completion rule coarse finePotentials _ bound
    (boundaryBound _ (SimpleGraph.Reachable.refl _)) bounded, ?_, ?_⟩
  · intro fine vertex retained
    dsimp only [potentials]
    rw [originalRecoveryGlobalPotential_level_completion]
    exact restriction fine vertex retained
  · apply (tendsto_add_atTop_iff_nat (coarse + 1)).mp
    have convergence := actual_fixed_coarse_trace_energy_tendsto_completion rule marks crossing growth growthPositive
      field fieldPositive fieldLimit coarse boundary
    apply convergence.congr' (Eventually.of_forall fun fine => ?_)
    try dsimp only [Function.comp_def, potentials]
    rw [show fine + (coarse + 1) = coarse + fine + 1 by omega,
      originalRecoveryGlobalPotential_level_completion]
    exact (minimizing fine).symm

end
end IGSIII34.Diffusion
