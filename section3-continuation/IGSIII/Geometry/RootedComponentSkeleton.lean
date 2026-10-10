import IGSIII.Geometry.OffsetSkeletonCompatibility

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- A single actual component, rooted at its original planted side. -/
def RetainedComponentVertex {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (sourceSide : Bool) :=
  {vertex : Fin vertices // (network.openGraph configuration).Reachable (plantedVertex network sourceSide) vertex}

@[reducible] def retainedComponentMetric {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (sourceSide : Bool) (values : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ values edge) (positive : ∀ edge, configuration edge = true → 0 < values edge) :
    MetricSpace (RetainedComponentVertex network configuration sourceSide) where
  dist first last := weightedDistance (network.openGraph configuration) (indexedBondCost network values) first.val last.val
  dist_self first := weightedDistance_self _ _ (indexedBondCost_nonnegative network values nonnegative) first.val
  dist_comm first last := weightedDistance_comm _ _ (indexedBondCost_nonnegative network values nonnegative) first.val last.val
  dist_triangle first middle last := weightedDistance_triangle _ _ (indexedBondCost_nonnegative network values nonnegative)
    (first.property.symm.trans middle.property) (middle.property.symm.trans last.property)
  eq_of_dist_eq_zero := fun {first last} zeroDistance => Subtype.ext
    (eq_of_weightedDistance_eq_zero_of_edge_positive _ _ (indexedBondCost_nonnegative network values nonnegative)
      (indexedBondCost_positive_on_open_edges network simple configuration values positive)
      (first.property.symm.trans last.property) zeroDistance)

def retainedComponentOldEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool) (depth : ℕ) :
    RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide ↪
      RetainedComponentVertex (rule.generation (depth + 1)).network (configuration (depth + 1)) sourceSide where
  toFun vertex := ⟨rule.generationOldVertex depth vertex.val, by
    rw [← generationOldVertex_planted rule depth sourceSide]
    apply (rule.generation_reachable_old_iff depth _ _ _).mpr
    rw [coherent depth]
    exact vertex.property⟩
  inj' := by
    intro first last sameImage
    exact Subtype.ext ((rule.generationOldVertex depth).injective (congrArg Subtype.val sameImage))

theorem retainedComponentTransition_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedComponentVertex (rule.generation first).network (configuration first) sourceSide) :
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide) first second bound vertex).val =
      persistentVertexEmbedding rule first second bound vertex.val := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [Universality.Geometry.IsometricSequence.transition, persistentVertexEmbedding,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound inductionHypothesis =>
    simp only [Universality.Geometry.IsometricSequence.transition, persistentVertexEmbedding,
      Function.Embedding.coeFn_mk, Nat.leRecOn_succ bound, retainedComponentOldEmbedding]
    exact congrArg (rule.generationOldVertex second) inductionHypothesis

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale) (offset : ℕ)
variable (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge)))

include scale scalePositive offset childConvergence in
theorem retainedComponentOldEmbedding_isometry (depth : ℕ) :
    letI := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
      (configuration depth) sourceSide (values depth) (nonnegative depth) (positive depth)
    letI := retainedComponentMetric (rule.generation (depth + 1)).network (classicalRule.generation (depth + 1)).simple
      (configuration (depth + 1)) sourceSide (values (depth + 1)) (nonnegative (depth + 1)) (positive (depth + 1))
    Isometry (retainedComponentOldEmbedding rule configuration coherent sourceSide depth) := by
  letI := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
    (configuration depth) sourceSide (values depth) (nonnegative depth) (positive depth)
  letI := retainedComponentMetric (rule.generation (depth + 1)).network (classicalRule.generation (depth + 1)).simple
    (configuration (depth + 1)) sourceSide (values (depth + 1)) (nonnegative (depth + 1)) (positive (depth + 1))
  apply Isometry.of_dist_eq
  intro first last
  exact actual_skeleton_weighted_distance_compatible_offset rule classicalRule configuration coherent scale scalePositive
    offset values childConvergence depth (first.property.symm.trans last.property)

/-- The actual intrinsic directed skeleton of either planted component,
including a single side of the shared noncrossing state. -/
def RootedComponentSkeleton (rule : Rule) (_classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (scale : ℝ) (_scalePositive : 0 < scale) (offset : ℕ)
    (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (_nonnegative : ∀ depth edge, 0 ≤ values depth edge)
    (_positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
    (_childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2 + offset)) atTop (𝓝 (values coarse edge))) : Type :=
  DirectLimit (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide))

instance rootedComponentSkeletonMetricSpace : MetricSpace (RootedComponentSkeleton rule classicalRule configuration coherent
    sourceSide scale scalePositive offset values nonnegative positive childConvergence) := by
  letI (depth : ℕ) := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
    (configuration depth) sourceSide (values depth) (nonnegative depth) (positive depth)
  exact Universality.Geometry.IsometricSequence.limitMetricSpace
    (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (retainedComponentOldEmbedding rule configuration coherent sourceSide)
    (retainedComponentOldEmbedding_isometry rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence)

def RootedComponentSpace : Type := UniformSpace.Completion (RootedComponentSkeleton rule classicalRule configuration coherent
  sourceSide scale scalePositive offset values nonnegative positive childConvergence)

instance rootedComponentSpaceMetricSpace : MetricSpace (RootedComponentSpace rule classicalRule configuration coherent
    sourceSide scale scalePositive offset values nonnegative positive childConvergence) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion (RootedComponentSkeleton rule classicalRule configuration coherent
    sourceSide scale scalePositive offset values nonnegative positive childConvergence)))

def rootedComponentVertex (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence :=
  UniformSpace.Completion.coe' (α := RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive offset
    values nonnegative positive childConvergence) ⟦⟨depth, vertex⟩⟧

theorem rootedComponentVertex_distance (depth : ℕ)
    (first last : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    dist (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence depth first)
      (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset
        values nonnegative positive childConvergence depth last) =
    weightedDistance ((rule.generation depth).network.openGraph (configuration depth))
      (indexedBondCost (rule.generation depth).network (values depth)) first.val last.val := by
  letI (depth : ℕ) := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
    (configuration depth) sourceSide (values depth) (nonnegative depth) (positive depth)
  exact (Universality.Geometry.IsometricSequence.completion_inclusion_isometry
    (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
    (retainedComponentOldEmbedding rule configuration coherent sourceSide)
    (retainedComponentOldEmbedding_isometry rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence) depth).dist_eq first last

end
end IGSIII.Geometry
