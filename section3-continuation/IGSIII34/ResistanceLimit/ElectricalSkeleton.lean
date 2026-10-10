import IGSIII34.ResistanceLimit.NetworkBounds
import IGSIII.Geometry.ActualChemicalSkeleton

/-!
The metric direct limit uses the actual retained vertices and the actual
persistent old-vertex maps. This deterministic constructor takes explicit
finite compatibility proofs; StationaryGeneration proves those proofs for
the model on an event of probability one. Compactness and the resistance-form
domain are further obligations, not assumptions of this construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
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

include compatible in
theorem electricalRetainedOldVertex_isometry (depth : ℕ) :
    letI := actualComponentResistanceMetric (rule.generation depth).network (configuration depth) (resistance depth) (positive depth)
    letI := actualComponentResistanceMetric (rule.generation (depth + 1)).network (configuration (depth + 1))
      (resistance (depth + 1)) (positive (depth + 1))
    Isometry (retainedOldVertexEmbedding rule configuration coherent depth) := by
  letI := actualComponentResistanceMetric (rule.generation depth).network (configuration depth) (resistance depth) (positive depth)
  letI := actualComponentResistanceMetric (rule.generation (depth + 1)).network (configuration (depth + 1))
    (resistance (depth + 1)) (positive (depth + 1))
  apply Isometry.of_dist_eq
  intro first last
  exact compatible depth first.val last.val (first.property.symm.trans last.property)

def ElectricalSkeleton (_resistance : ∀ depth,
    {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
    (_positive : ∀ depth edge, 0 < _resistance depth edge)
    (_compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
      pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
          (_resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
        pairResistance (network (rule.generation depth).network (configuration depth)) (_resistance depth) first last) :=
  DirectLimit (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent))

instance electricalSkeletonMetricSpace :
    MetricSpace (ElectricalSkeleton rule configuration coherent resistance positive compatible) := by
  letI (depth : ℕ) := actualComponentResistanceMetric (rule.generation depth).network
    (configuration depth) (resistance depth) (positive depth)
  exact Universality.Geometry.IsometricSequence.limitMetricSpace
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent)
    (electricalRetainedOldVertex_isometry rule configuration coherent resistance positive compatible)

def ElectricalSpace := UniformSpace.Completion (ElectricalSkeleton rule configuration coherent resistance positive compatible)

instance electricalSpaceMetricSpace : MetricSpace (ElectricalSpace rule configuration coherent resistance positive compatible) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion (ElectricalSkeleton rule configuration coherent resistance positive compatible)))

instance electricalSpaceCompleteSpace : CompleteSpace (ElectricalSpace rule configuration coherent resistance positive compatible) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (ElectricalSkeleton rule configuration coherent resistance positive compatible)))

def electricalVertex (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    ElectricalSpace rule configuration coherent resistance positive compatible :=
  UniformSpace.Completion.coe' (α := ElectricalSkeleton rule configuration coherent resistance positive compatible) ⟦⟨depth, vertex⟩⟧

theorem electricalVertex_distance (depth : ℕ)
    (first last : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    dist (electricalVertex rule configuration coherent resistance positive compatible depth first)
      (electricalVertex rule configuration coherent resistance positive compatible depth last) =
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first.val last.val := by
  letI (depth : ℕ) := actualComponentResistanceMetric (rule.generation depth).network
    (configuration depth) (resistance depth) (positive depth)
  exact (Universality.Geometry.IsometricSequence.completion_inclusion_isometry
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent)
    (electricalRetainedOldVertex_isometry rule configuration coherent resistance positive compatible) depth).dist_eq first last

theorem electricalVertex_old (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    electricalVertex rule configuration coherent resistance positive compatible depth vertex =
      electricalVertex rule configuration coherent resistance positive compatible (depth + 1)
        (retainedOldVertexEmbedding rule configuration coherent depth vertex) := by
  apply congrArg (fun point : ElectricalSkeleton rule configuration coherent resistance positive compatible =>
    UniformSpace.Completion.coe' point)
  have persistent := DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [ElectricalSkeleton, Universality.Geometry.IsometricSequence.transition,
    Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using persistent.symm

theorem electricalVertex_dense :
    Dense (⋃ depth, Set.range (electricalVertex rule configuration coherent resistance positive compatible depth)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := ElectricalSkeleton rule configuration coherent resistance positive compatible)).mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) point
  exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

end
end IGSIII34.ResistanceLimit
