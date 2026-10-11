import IGSIII34.Forms.FiniteTraceUniqueness
import IGSIII34.ResistanceLimit.SkeletonVertexExhaustion

/-! Uniqueness on the actual increasing retained vertex sets. The hypotheses
on the competing form say precisely that its finite restrictions have the
given trace minima; exhaustion of the domain and equality of limiting energy
are conclusions, not hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII34.Percolation
open IGSIII.Chemical.Substitution

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem skeleton_form_unique_from_finite_traces
    (energyCompatible : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth))
          (resistance depth) (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
        sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
          (resistance (depth + 1)) potential)
    {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (anchor : ElectricalSkeleton rule configuration coherent resistance positive compatible)
    (evaluation : Energy →ₗ[ℝ] (ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ))
    (injective : Function.Injective evaluation)
    (continuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (lower : ∀ boundary depth potential,
      (∀ vertex, evaluation potential (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex) =
        boundary (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex)) →
      traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
          (skeletonEnergyConductance rule configuration resistance) depth boundary + boundary anchor ^ 2 ≤ ‖potential‖ ^ 2)
    (attained : ∀ boundary depth, ∃ potential,
      (∀ vertex, evaluation potential (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex) =
        boundary (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex)) ∧
      ‖potential‖ ^ 2 = traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
          (skeletonEnergyConductance rule configuration resistance) depth boundary + boundary anchor ^ 2) :
    Set.range evaluation = (energyDomain
        (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive) :
          Set (ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ)) ∧
      ∀ potential, ‖potential‖ ^ 2 - evaluation potential anchor ^ 2 =
        limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
          (skeletonEnergyConductance rule configuration resistance) (evaluation potential) := by
  apply IGSIII34.Forms.finite_trace_form_unique
    (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
    (skeletonEnergyConductance rule configuration resistance)
    (skeletonEnergyConductance_nonnegative rule configuration resistance positive)
    (skeleton_traceEnergy_monotone rule configuration coherent resistance positive compatible energyCompatible)
    anchor evaluation injective continuous
    (fun depth => Set.range (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth))
    (skeleton_vertex_ranges_monotone rule configuration coherent resistance positive compatible)
    (skeleton_vertex_ranges_exhaustive rule configuration coherent resistance positive compatible)
  · intro boundary depth potential agrees
    exact lower boundary depth potential (fun vertex => agrees _ ⟨vertex, rfl⟩)
  · intro boundary depth
    obtain ⟨potential, agrees, minimum⟩ := attained boundary depth
    refine ⟨potential, ?_, minimum⟩
    rintro point ⟨vertex, rfl⟩
    exact agrees vertex

end
end IGSIII34.ResistanceLimit
