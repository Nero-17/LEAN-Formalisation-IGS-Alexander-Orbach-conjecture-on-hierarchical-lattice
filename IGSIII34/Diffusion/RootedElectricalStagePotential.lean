import IGSIII34.Diffusion.RootedElectricalIntrinsicEnergy
import IGSIII34.ResistanceLimit.SelectedComponentEnergy
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem rootedElectricalSkeletonVertex_old (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth vertex =
      rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible (depth + 1)
        (retainedComponentOldEmbedding rule configuration coherent sourceSide depth vertex) := by
  have persistent := DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [rootedElectricalSkeletonVertex, Universality.Geometry.IsometricSequence.transition,
    Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using persistent.symm

theorem rootedElectricalSkeletonPoint_old (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible (depth + 1)
        (rule.generationOldVertex depth vertex) =
      rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth vertex := by
  have retainedFine : ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (plantedVertex (rule.generation (depth + 1)).network sourceSide) (rule.generationOldVertex depth vertex) ↔
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (plantedVertex (rule.generation depth).network sourceSide) vertex := by
    rw [← generationOldVertex_planted rule depth sourceSide, rule.generation_reachable_old_iff, coherent depth]
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex
  · simp only [rootedElectricalSkeletonPoint, dif_pos retained, dif_pos (retainedFine.mpr retained)]
    exact (rootedElectricalSkeletonVertex_old rule configuration coherent sourceSide resistance positive compatible depth ⟨vertex, retained⟩).symm
  · simp only [rootedElectricalSkeletonPoint, dif_neg retained, dif_neg (mt retainedFine.mp retained)]
    have planted := rootedElectricalSkeletonVertex_old rule configuration coherent sourceSide resistance positive compatible depth
      ⟨plantedVertex (rule.generation depth).network sourceSide, SimpleGraph.Reachable.refl _⟩
    have sameVertex : retainedComponentOldEmbedding rule configuration coherent sourceSide depth
        ⟨plantedVertex (rule.generation depth).network sourceSide, SimpleGraph.Reachable.refl _⟩ =
        ⟨plantedVertex (rule.generation (depth + 1)).network sourceSide, SimpleGraph.Reachable.refl _⟩ :=
      Subtype.ext (generationOldVertex_planted rule depth sourceSide)
    rw [sameVertex] at planted
    exact planted.symm

/-- The genuine all-vertex stage potential, zero outside the selected side. -/
def rootedElectricalStagePotential
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) : ℝ :=
  if retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex then
    potential (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth ⟨vertex, retained⟩)
  else 0

theorem rootedElectricalStagePotential_old
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential (depth + 1)
      (rule.generationOldVertex depth vertex) =
    rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth vertex := by
  have retainedFine : ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (plantedVertex (rule.generation (depth + 1)).network sourceSide) (rule.generationOldVertex depth vertex) ↔
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (plantedVertex (rule.generation depth).network sourceSide) vertex := by
    rw [← generationOldVertex_planted rule depth sourceSide, rule.generation_reachable_old_iff, coherent depth]
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex
  · simp only [rootedElectricalStagePotential, dif_pos retained, dif_pos (retainedFine.mpr retained)]
    exact congrArg potential (rootedElectricalSkeletonVertex_old rule configuration coherent sourceSide resistance positive compatible depth ⟨vertex, retained⟩).symm
  · simp only [rootedElectricalStagePotential, dif_neg retained, dif_neg (mt retainedFine.mp retained)]

theorem rootedElectricalStagePotential_projection
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) (depth : ℕ) :
    sourceProjection (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide)
      (rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth) =
      rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth := by
  funext vertex
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex
  · simp only [sourceProjection, sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source, if_pos retained]
  · simp only [sourceProjection, sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source,
      if_neg retained, rootedElectricalStagePotential, dif_neg retained]

theorem rootedElectricalSkeletonPoint_projection
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) (depth : ℕ) :
    sourceProjection (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide)
      (fun vertex => potential (rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth vertex)) =
      rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth := by
  funext vertex
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex
  · simp only [sourceProjection, sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source, if_pos retained,
      rootedElectricalSkeletonPoint, dif_pos retained, rootedElectricalStagePotential]
  · simp only [sourceProjection, sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source,
      if_neg retained, rootedElectricalStagePotential, dif_neg retained]

/-- No energy is added by writing a local skeleton potential on all finite
vertices with zero values outside its retained component. -/
theorem rootedElectricalStagePotential_energy
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) (depth : ℕ) :
    sourceComponentEnergy (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide)
      (resistance depth) (rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth) =
    rootedElectricalIntrinsicTraceEnergy rule configuration coherent sourceSide resistance positive compatible depth potential := by
  rw [rootedElectricalIntrinsicTraceEnergy, sourceComponentEnergy_eq_projectedEnergy,
    sourceComponentEnergy_eq_projectedEnergy, rootedElectricalStagePotential_projection, rootedElectricalSkeletonPoint_projection]

end
end IGSIII34.Diffusion
