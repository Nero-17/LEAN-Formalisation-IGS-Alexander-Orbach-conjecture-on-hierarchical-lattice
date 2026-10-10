import IGSIII.Geometry.RootedComponentSkeleton

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

instance retainedComponentVertexFinite {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (sourceSide : Bool) : Finite (RetainedComponentVertex network configuration sourceSide) :=
  inferInstanceAs (Finite {vertex : Fin vertices // (network.openGraph configuration).Reachable (plantedVertex network sourceSide) vertex})

def retainedComponentPersistentEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (first second : ℕ) (bound : first ≤ second) :
    RetainedComponentVertex (rule.generation first).network (configuration first) sourceSide ↪
      RetainedComponentVertex (rule.generation second).network (configuration second) sourceSide where
  toFun vertex := ⟨persistentVertexEmbedding rule first second bound vertex.val, by
    rw [← persistentVertexEmbedding_planted rule first second bound sourceSide]
    exact (persistentVertexEmbedding_reachable_iff rule configuration coherent first second bound _ _).mpr vertex.property⟩
  inj' := by
    intro first last equality
    exact Subtype.ext ((persistentVertexEmbedding rule _ _ bound).injective (congrArg Subtype.val equality))

@[simp] theorem retainedComponentPersistentEmbedding_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedComponentVertex (rule.generation first).network (configuration first) sourceSide) :
    (retainedComponentPersistentEmbedding rule configuration coherent sourceSide first second bound vertex).val =
      persistentVertexEmbedding rule first second bound vertex.val := rfl
theorem retainedComponentPersistentEmbedding_eq_transition (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (first second : ℕ) (bound : first ≤ second) :
    retainedComponentPersistentEmbedding rule configuration coherent sourceSide first second bound =
      Universality.Geometry.IsometricSequence.transition
        (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
        (retainedComponentOldEmbedding rule configuration coherent sourceSide) first second bound := by
  apply Function.Embedding.ext
  intro vertex
  exact Subtype.ext (retainedComponentTransition_val rule configuration coherent sourceSide first second bound vertex).symm

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

theorem rootedComponentVertex_persistent (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedComponentVertex (rule.generation first).network (configuration first) sourceSide) :
    rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence first vertex =
    rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence second
      (retainedComponentPersistentEmbedding rule configuration coherent sourceSide first second bound vertex) := by
  apply congrArg (fun point : RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive offset values
    nonnegative positive childConvergence => UniformSpace.Completion.coe' point)
  rw [retainedComponentPersistentEmbedding_eq_transition]
  exact (DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) first second vertex bound).symm

theorem rootedComponentVertex_dense :
    Dense (⋃ depth, Set.range (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset
      values nonnegative positive childConvergence depth)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := RootedComponentSkeleton rule classicalRule configuration coherent sourceSide
    scale scalePositive offset values nonnegative positive childConvergence)).mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) point
  exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

instance rootedComponentSpaceCompleteSpace : CompleteSpace (RootedComponentSpace rule classicalRule configuration coherent sourceSide
    scale scalePositive offset values nonnegative positive childConvergence) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (RootedComponentSkeleton rule classicalRule configuration coherent sourceSide
    scale scalePositive offset values nonnegative positive childConvergence)))

instance rootedComponentSpaceNonempty : Nonempty (RootedComponentSpace rule classicalRule configuration coherent sourceSide
    scale scalePositive offset values nonnegative positive childConvergence) :=
  ⟨rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive offset values nonnegative positive childConvergence
    0 ⟨plantedVertex (rule.generation 0).network sourceSide, SimpleGraph.Reachable.refl _⟩⟩

end
end IGSIII.Geometry

