import IGSIII.Geometry.ActualSkeletonLimits

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

instance retainedSkeletonVertexFinite {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) :
    Finite (RetainedSkeletonVertex network configuration) :=
  inferInstanceAs (Finite {vertex : Fin vertices // (network.openGraph configuration).Reachable network.source vertex})

def retainedOldVertexEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (depth : ℕ) :
    RetainedSkeletonVertex (rule.generation depth).network (configuration depth) ↪
      RetainedSkeletonVertex (rule.generation (depth + 1)).network (configuration (depth + 1)) where
  toFun vertex := ⟨rule.generationOldVertex depth vertex.val, by
    change ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (rule.generationOldVertex depth (rule.generation depth).network.source) (rule.generationOldVertex depth vertex.val)
    apply (rule.generation_reachable_old_iff depth _ _ _).mpr
    rw [coherent depth]
    exact vertex.property⟩
  inj' := by
    intro first last equality
    exact Subtype.ext ((rule.generationOldVertex depth).injective (congrArg Subtype.val equality))

theorem retainedOldVertexEmbedding_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    (retainedOldVertexEmbedding rule configuration coherent depth vertex).val = rule.generationOldVertex depth vertex.val := rfl

def retainedPersistentVertexEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (first second : ℕ) (bound : first ≤ second) :
    RetainedSkeletonVertex (rule.generation first).network (configuration first) ↪
      RetainedSkeletonVertex (rule.generation second).network (configuration second) where
  toFun vertex := ⟨persistentVertexEmbedding rule first second bound vertex.val, by
    have source_identity := persistentVertexEmbedding_planted rule first second bound true
    change persistentVertexEmbedding rule first second bound (rule.generation first).network.source =
      (rule.generation second).network.source at source_identity
    rw [← source_identity]
    exact (persistentVertexEmbedding_reachable_iff rule configuration coherent first second bound _ _).mpr vertex.property⟩
  inj' := by
    intro first last equality
    exact Subtype.ext ((persistentVertexEmbedding rule _ _ bound).injective (congrArg Subtype.val equality))

theorem retainedPersistentVertexEmbedding_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    (retainedPersistentVertexEmbedding rule configuration coherent first second bound vertex).val =
      persistentVertexEmbedding rule first second bound vertex.val := rfl

theorem retainedTransition_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent) first second bound vertex).val =
        persistentVertexEmbedding rule first second bound vertex.val := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [Universality.Geometry.IsometricSequence.transition, persistentVertexEmbedding,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound induction_hypothesis =>
    simp only [Universality.Geometry.IsometricSequence.transition, persistentVertexEmbedding,
      Function.Embedding.coeFn_mk, Nat.leRecOn_succ bound, retainedOldVertexEmbedding_val]
    exact congrArg (rule.generationOldVertex second) induction_hypothesis

theorem retainedPersistentVertexEmbedding_eq_transition (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (first second : ℕ) (bound : first ≤ second) :
    retainedPersistentVertexEmbedding rule configuration coherent first second bound =
      Universality.Geometry.IsometricSequence.transition
        (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
        (retainedOldVertexEmbedding rule configuration coherent) first second bound := by
  apply Function.Embedding.ext
  intro vertex
  exact Subtype.ext (retainedTransition_val rule configuration coherent first second bound vertex).symm

variable (rule : Rule) (classical : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))

include scale_positive child_convergence in
theorem retainedOldVertexEmbedding_isometry (depth : ℕ) :
    letI := actualSkeletonMetric (rule.generation depth).network (classical.generation depth).simple
      (configuration depth) (limit_length depth) (nonnegative depth) (positive depth)
    letI := actualSkeletonMetric (rule.generation (depth + 1)).network (classical.generation (depth + 1)).simple
      (configuration (depth + 1)) (limit_length (depth + 1)) (nonnegative (depth + 1)) (positive (depth + 1))
    Isometry (retainedOldVertexEmbedding rule configuration coherent depth) := by
  letI := actualSkeletonMetric (rule.generation depth).network (classical.generation depth).simple
    (configuration depth) (limit_length depth) (nonnegative depth) (positive depth)
  letI := actualSkeletonMetric (rule.generation (depth + 1)).network (classical.generation (depth + 1)).simple
    (configuration (depth + 1)) (limit_length (depth + 1)) (nonnegative (depth + 1)) (positive (depth + 1))
  apply Isometry.of_dist_eq
  intro first last
  exact actual_skeleton_weighted_distance_compatible rule classical configuration coherent scale scale_positive
    limit_length child_convergence depth (first.property.symm.trans last.property)

/-- The directed union of actual retained finite chemical skeletons. -/
def ActualChemicalSkeleton (rule : Rule) (_classical : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (_scale_positive : 0 < scale)
    (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (_nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
    (_positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
    (_child_convergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge))) : Type :=
  DirectLimit (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent))

/-- The metric is the proved compatible weighted shortest-path metric. -/
instance actualChemicalSkeletonMetricSpace : MetricSpace (ActualChemicalSkeleton rule classical configuration coherent
    scale scale_positive limit_length nonnegative positive child_convergence) := by
  letI (depth : ℕ) := actualSkeletonMetric (rule.generation depth).network (classical.generation depth).simple
    (configuration depth) (limit_length depth) (nonnegative depth) (positive depth)
  exact Universality.Geometry.IsometricSequence.limitMetricSpace
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent)
    (retainedOldVertexEmbedding_isometry rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence)

def ActualChemicalSpace : Type :=
  UniformSpace.Completion (ActualChemicalSkeleton rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence)

instance actualChemicalSpaceMetricSpace : MetricSpace (ActualChemicalSpace rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence) := by
  exact inferInstanceAs (MetricSpace (UniformSpace.Completion (ActualChemicalSkeleton rule classical configuration coherent
    scale scale_positive limit_length nonnegative positive child_convergence)))

def actualChemicalVertex (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    ActualChemicalSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence :=
  UniformSpace.Completion.coe' (α := ActualChemicalSkeleton rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence) ⟦⟨depth, vertex⟩⟧

instance actualChemicalSpaceNonempty : Nonempty (ActualChemicalSpace rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence) :=
  ⟨actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
    0 ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩⟩

theorem actualChemicalVertex_distance (depth : ℕ)
    (first last : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    letI := actualChemicalSpaceMetricSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence
    dist (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth first)
      (actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth last) =
        weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
          (indexedBondCost (rule.generation depth).network (limit_length depth)) first.val last.val := by
  letI (depth : ℕ) := actualSkeletonMetric (rule.generation depth).network (classical.generation depth).simple
    (configuration depth) (limit_length depth) (nonnegative depth) (positive depth)
  exact (Universality.Geometry.IsometricSequence.completion_inclusion_isometry
    (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
    (retainedOldVertexEmbedding rule configuration coherent)
    (retainedOldVertexEmbedding_isometry rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence) depth).dist_eq first last

instance actualChemicalSpaceCompleteSpace : CompleteSpace (ActualChemicalSpace rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (ActualChemicalSkeleton rule classical configuration coherent
    scale scale_positive limit_length nonnegative positive child_convergence)))

theorem actualChemicalVertex_old (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence depth vertex =
      actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
        (depth + 1) (retainedOldVertexEmbedding rule configuration coherent depth vertex) := by
  apply congrArg (fun point : ActualChemicalSkeleton rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence => UniformSpace.Completion.coe' point)
  have persistent := DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [Universality.Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using persistent.symm

theorem actualChemicalVertex_dense :
    Dense (⋃ depth, Set.range (actualChemicalVertex rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence depth)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := ActualChemicalSkeleton rule classical configuration coherent
    scale scale_positive limit_length nonnegative positive child_convergence)).mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) point
  exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

theorem actualChemicalVertex_persistent (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence first vertex =
      actualChemicalVertex rule classical configuration coherent scale scale_positive limit_length nonnegative positive child_convergence
        second (retainedPersistentVertexEmbedding rule configuration coherent first second bound vertex) := by
  apply congrArg (fun point : ActualChemicalSkeleton rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence => UniformSpace.Completion.coe' point)
  rw [retainedPersistentVertexEmbedding_eq_transition]
  exact (DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) first second vertex bound).symm

end
end IGSIII.Geometry
