import IGSIII34.ResistanceLimit.SkeletonEnergy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

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
variable (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
  ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
    (∀ vertex, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (rule.generation depth).network.source vertex →
      potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
    sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) potential =
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) boundary)

def harmonicTower (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth) : Fin (rule.generation depth).vertices → ℝ :=
  Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices → ℝ) bound
    (fun {depth} potential => Classical.choose (minimizer depth potential)) boundary

theorem harmonicTower_step (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth) :
    harmonicTower rule configuration resistance minimizer initial boundary (depth + 1) (Nat.le_succ_of_le bound) =
      Classical.choose (minimizer depth (harmonicTower rule configuration resistance minimizer initial boundary depth bound)) := by
  unfold harmonicTower
  rw [Nat.leRecOn_succ bound]

theorem harmonicTower_energy (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth) :
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
      (harmonicTower rule configuration resistance minimizer initial boundary depth bound) =
    sourceComponentEnergy (network (rule.generation initial).network (configuration initial)) (resistance initial) boundary := by
  induction depth, bound using Nat.le_induction with
  | base => simp only [harmonicTower, Nat.leRecOn_self]
  | succ depth bound inductionHypothesis =>
    rw [harmonicTower_step]
    exact (Classical.choose_spec (minimizer depth
      (harmonicTower rule configuration resistance minimizer initial boundary depth bound))).2.trans inductionHypothesis

theorem harmonicTower_step_retained (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    harmonicTower rule configuration resistance minimizer initial boundary (depth + 1) (Nat.le_succ_of_le bound)
      (rule.generationOldVertex depth vertex.val) =
    harmonicTower rule configuration resistance minimizer initial boundary depth bound vertex.val := by
  rw [harmonicTower_step]
  exact (Classical.choose_spec (minimizer depth
    (harmonicTower rule configuration resistance minimizer initial boundary depth bound))).1 vertex.val vertex.property

theorem harmonicTower_persistent (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (first last : ℕ) (initialBound : initial ≤ first) (bound : first ≤ last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    harmonicTower rule configuration resistance minimizer initial boundary last (initialBound.trans bound)
      (retainedPersistentVertexEmbedding rule configuration coherent first last bound vertex).val =
    harmonicTower rule configuration resistance minimizer initial boundary first initialBound vertex.val := by
  induction last, bound using Nat.le_induction with
  | base => simp only [retainedPersistentVertexEmbedding_val, persistentVertexEmbedding,
      Universality.Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ last bound inductionHypothesis =>
    rw [retainedPersistentVertexEmbedding_val,
      ← persistentVertexEmbedding_trans rule first last (last + 1) bound (Nat.le_succ last),
      persistentVertexEmbedding_next]
    exact (harmonicTower_step_retained rule configuration resistance minimizer initial boundary last
      (initialBound.trans bound) (retainedPersistentVertexEmbedding rule configuration coherent first last bound vertex)).trans
      inductionHypothesis

def harmonicTowerStage (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) : ℝ :=
  harmonicTower rule configuration resistance minimizer initial boundary (max initial depth) (le_max_left _ _)
    (retainedPersistentVertexEmbedding rule configuration coherent depth (max initial depth) (le_max_right _ _) vertex).val

theorem harmonicTowerStage_compatible (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (first last : ℕ) (bound : first ≤ last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    harmonicTowerStage rule configuration coherent resistance minimizer initial boundary first vertex =
    harmonicTowerStage rule configuration coherent resistance minimizer initial boundary last
      (Universality.Geometry.IsometricSequence.transition
        (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
        (retainedOldVertexEmbedding rule configuration coherent) first last bound vertex) := by
  unfold harmonicTowerStage
  have persistent := harmonicTower_persistent rule configuration coherent resistance minimizer initial boundary
    (max initial first) (max initial last) (le_max_left _ _) (max_le_max_left initial bound)
    (retainedPersistentVertexEmbedding rule configuration coherent first (max initial first) (le_max_right _ _) vertex)
  rw [retainedPersistentVertexEmbedding_val, retainedPersistentVertexEmbedding_val,
    persistentVertexEmbedding_trans] at persistent
  have projectedValue : (retainedPersistentVertexEmbedding rule configuration coherent last (max initial last)
      (le_max_right _ _) (Universality.Geometry.IsometricSequence.transition
        (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
        (retainedOldVertexEmbedding rule configuration coherent) first last bound vertex)).val =
      persistentVertexEmbedding rule first (max initial last) (bound.trans (le_max_right _ _)) vertex.val := by
    calc
      _ = persistentVertexEmbedding rule last (max initial last) (le_max_right _ _)
          (Universality.Geometry.IsometricSequence.transition
            (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
            (retainedOldVertexEmbedding rule configuration coherent) first last bound vertex).val :=
        retainedPersistentVertexEmbedding_val rule configuration coherent last (max initial last) _ _
      _ = persistentVertexEmbedding rule last (max initial last) (le_max_right _ _)
          (persistentVertexEmbedding rule first last bound vertex.val) := congrArg _
        (retainedTransition_val rule configuration coherent first last bound vertex)
      _ = _ := persistentVertexEmbedding_trans rule first last (max initial last) bound (le_max_right _ _) vertex.val
  rw [retainedPersistentVertexEmbedding_val]
  exact persistent.symm.trans (congrArg
    (harmonicTower rule configuration resistance minimizer initial boundary (max initial last) (le_max_left _ _))
    projectedValue).symm

def harmonicTowerFunction (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ :=
  DirectLimit.lift (Universality.Geometry.IsometricSequence.transition
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent))
    (harmonicTowerStage rule configuration coherent resistance minimizer initial boundary)
    (harmonicTowerStage_compatible rule configuration coherent resistance minimizer initial boundary)

theorem harmonicTowerFunction_retained (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex) =
    harmonicTower rule configuration resistance minimizer initial boundary depth bound vertex.val := by
  change harmonicTower rule configuration resistance minimizer initial boundary (max initial depth) (le_max_left _ _)
    (retainedPersistentVertexEmbedding rule configuration coherent depth (max initial depth) (le_max_right _ _) vertex).val = _
  exact harmonicTower_persistent rule configuration coherent resistance minimizer initial boundary
    depth (max initial depth) bound (le_max_right _ _) vertex

theorem sourceComponentEnergy_congr_retained {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) (first last : Vertex → ℝ)
    (equal : ∀ vertex, network.graph.Reachable network.source vertex → first vertex = last vertex) :
    sourceComponentEnergy network resistance first = sourceComponentEnergy network resistance last := by
  rw [sourceComponentEnergy_eq_projectedEnergy, sourceComponentEnergy_eq_projectedEnergy]
  congr 1
  funext vertex
  by_cases retained : network.graph.Reachable network.source vertex
  · simp only [sourceProjection, if_pos retained, equal vertex retained]
  · simp only [sourceProjection, if_neg retained]

theorem harmonicTowerFunction_trace_energy (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (depth : ℕ) (bound : initial ≤ depth) :
    traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) depth
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary) =
    sourceComponentEnergy (network (rule.generation initial).network (configuration initial)) (resistance initial) boundary := by
  rw [skeleton_traceEnergy_eq_source_energy]
  refine (sourceComponentEnergy_congr_retained _ _ _
    (harmonicTower rule configuration resistance minimizer initial boundary depth bound) ?_).trans
    (harmonicTower_energy rule configuration resistance minimizer initial boundary depth bound)
  intro vertex retained
  have retained' : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source vertex := by
    rw [graph_eq_openGraph] at retained
    exact retained
  rw [electricalSkeletonPoint_retained rule configuration coherent resistance positive compatible depth ⟨vertex, retained'⟩]
  exact harmonicTowerFunction_retained rule configuration coherent resistance positive compatible minimizer initial boundary
    depth bound ⟨vertex, retained'⟩

theorem harmonicTowerFunction_finite
    (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
        (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) potential)
    (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary ∈
      energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive) := by
  refine ⟨sourceComponentEnergy (network (rule.generation initial).network (configuration initial))
    (resistance initial) boundary, ?_⟩
  rintro value ⟨depth, rfl⟩
  have bound := skeleton_traceEnergy_monotone rule configuration coherent resistance positive compatible sourceEnergyLe
    (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary)
    (le_max_right initial depth)
  exact bound.trans (harmonicTowerFunction_trace_energy rule configuration coherent resistance positive compatible minimizer
    initial boundary (max initial depth) (le_max_left _ _)).le

theorem harmonicTowerFunction_boundary (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial)) :
    harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) =
      boundary vertex.val := by
  have values := harmonicTowerFunction_retained rule configuration coherent resistance positive compatible minimizer
    initial boundary initial le_rfl vertex
  simpa only [harmonicTower, Nat.leRecOn_self] using values

theorem harmonicTowerFunction_limiting_energy
    (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
        (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) potential)
    (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary) =
      sourceComponentEnergy (network (rule.generation initial).network (configuration initial)) (resistance initial) boundary := by
  apply le_antisymm
  · apply ciSup_le
    intro depth
    have bound := skeleton_traceEnergy_monotone rule configuration coherent resistance positive compatible sourceEnergyLe
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary)
      (le_max_right initial depth)
    exact bound.trans (harmonicTowerFunction_trace_energy rule configuration coherent resistance positive compatible minimizer
      initial boundary (max initial depth) (le_max_left _ _)).le
  · rw [← harmonicTowerFunction_trace_energy rule configuration coherent resistance positive compatible minimizer
      initial boundary initial le_rfl]
    exact traceEnergy_le_limitingEnergy _ _ _
      (harmonicTowerFunction_finite rule configuration coherent resistance positive compatible minimizer sourceEnergyLe
        initial boundary) initial

end
end IGSIII34.ResistanceLimit
