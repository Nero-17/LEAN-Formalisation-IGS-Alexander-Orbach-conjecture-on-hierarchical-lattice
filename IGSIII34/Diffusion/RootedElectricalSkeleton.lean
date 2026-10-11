import IGSIII34.ResistanceLimit.NetworkBounds
import IGSIII.Geometry.RootedComponentSkeleton

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

/-- The actual intrinsic electrical metric on either planted component. -/
@[reducible] def rootedComponentResistanceMetric {vertices edges : ℕ}
    (original : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) (sourceSide : Bool)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    MetricSpace (RetainedComponentVertex original configuration sourceSide) where
  dist first last := pairResistance (network original configuration) resistance first.val last.val
  dist_self first := pairResistance_self _ _ _
  dist_comm first last := pairResistance_comm _ _ positive (by
    rw [graph_eq_openGraph]
    exact first.property.symm.trans last.property)
  dist_triangle first middle last := pairResistance_triangle _ _ positive _ _ _ (by
    rw [graph_eq_openGraph]
    exact first.property.symm.trans middle.property) (by
    rw [graph_eq_openGraph]
    exact middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := by
    intro first last zero
    apply Subtype.ext
    by_contra distinct
    have strict := pairResistance_pos (network original configuration) resistance positive distinct (by
      rw [graph_eq_openGraph]
      exact first.property.symm.trans last.property)
    exact (ne_of_gt strict) zero

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

include compatible in
theorem rootedElectricalOldVertex_isometry (depth : ℕ) :
    letI := rootedComponentResistanceMetric (rule.generation depth).network (configuration depth) sourceSide (resistance depth) (positive depth)
    letI := rootedComponentResistanceMetric (rule.generation (depth + 1)).network (configuration (depth + 1)) sourceSide
      (resistance (depth + 1)) (positive (depth + 1))
    Isometry (retainedComponentOldEmbedding rule configuration coherent sourceSide depth) := by
  letI := rootedComponentResistanceMetric (rule.generation depth).network (configuration depth) sourceSide (resistance depth) (positive depth)
  letI := rootedComponentResistanceMetric (rule.generation (depth + 1)).network (configuration (depth + 1)) sourceSide
    (resistance (depth + 1)) (positive (depth + 1))
  apply Isometry.of_dist_eq
  intro first last
  exact compatible depth first.val last.val (first.property.symm.trans last.property)

def RootedElectricalSkeleton (_resistance : ∀ depth,
    {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
    (_positive : ∀ depth edge, 0 < _resistance depth edge)
    (_compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
      pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
          (_resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
        pairResistance (network (rule.generation depth).network (configuration depth)) (_resistance depth) first last) :=
  DirectLimit (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide))

instance rootedElectricalSkeletonMetricSpace :
    MetricSpace (RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible) := by
  letI (depth : ℕ) := rootedComponentResistanceMetric (rule.generation depth).network
    (configuration depth) sourceSide (resistance depth) (positive depth)
  exact Universality.Geometry.IsometricSequence.limitMetricSpace
    (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (retainedComponentOldEmbedding rule configuration coherent sourceSide)
    (rootedElectricalOldVertex_isometry rule configuration coherent sourceSide resistance positive compatible)

def RootedElectricalSpace := UniformSpace.Completion (RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible)

instance rootedElectricalSpaceMetricSpace : MetricSpace (RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion (RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible)))

instance rootedElectricalSpaceCompleteSpace : CompleteSpace (RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible)))

def rootedElectricalVertex (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible :=
  UniformSpace.Completion.coe' (α := RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible) ⟦⟨depth, vertex⟩⟧

theorem rootedElectricalVertex_distance (depth : ℕ)
    (first last : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    dist (rootedElectricalVertex rule configuration coherent sourceSide resistance positive compatible depth first)
      (rootedElectricalVertex rule configuration coherent sourceSide resistance positive compatible depth last) =
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first.val last.val := by
  letI (depth : ℕ) := rootedComponentResistanceMetric (rule.generation depth).network
    (configuration depth) sourceSide (resistance depth) (positive depth)
  exact (Universality.Geometry.IsometricSequence.completion_inclusion_isometry
    (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (retainedComponentOldEmbedding rule configuration coherent sourceSide)
    (rootedElectricalOldVertex_isometry rule configuration coherent sourceSide resistance positive compatible) depth).dist_eq first last

theorem rootedElectricalVertex_old (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    rootedElectricalVertex rule configuration coherent sourceSide resistance positive compatible depth vertex =
      rootedElectricalVertex rule configuration coherent sourceSide resistance positive compatible (depth + 1)
        (retainedComponentOldEmbedding rule configuration coherent sourceSide depth vertex) := by
  apply congrArg (fun point : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible =>
    UniformSpace.Completion.coe' point)
  have persistent := DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [RootedElectricalSkeleton, Universality.Geometry.IsometricSequence.transition,
    Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using persistent.symm

theorem rootedElectricalVertex_dense :
    Dense (⋃ depth, Set.range (rootedElectricalVertex rule configuration coherent sourceSide resistance positive compatible depth)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible)).mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) point
  exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

end
end IGSIII34.Diffusion
