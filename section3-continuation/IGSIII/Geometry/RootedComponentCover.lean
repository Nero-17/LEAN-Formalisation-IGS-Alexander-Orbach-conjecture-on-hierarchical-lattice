import IGSIII.Geometry.RootedComponentNets

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology
variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (address : List (Fin rule.edges)) (opened : Bool)
variable (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth address opened)
variable (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + address.length)) atTop (𝓝 (values coarse edge)))

include opened configurationIdentity in
theorem rootedComponentSpace_near_birth_skeleton
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (age : ℕ) (beyond : start ≤ address.length + age + 1)
    (point : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence) :
    ∃ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      dist point (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence age anchor) ≤ coefficient * eta ^ (address.length + age + 1) := by
  have coverClosed : IsClosed (⋃ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
      Metric.closedBall (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence age anchor) (coefficient * eta ^ (address.length + age + 1))) :=
    isClosed_iUnion_of_finite (fun _ => Metric.isClosed_closedBall)
  have coverVertices : (⋃ depth, Set.range (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
      values nonnegative positive childConvergence depth)) ⊆
      ⋃ anchor : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide,
        Metric.closedBall (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive address.length
          values nonnegative positive childConvergence age anchor) (coefficient * eta ^ (address.length + age + 1)) := by
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    rcases le_total age depth with bound | bound
    · obtain ⟨anchor, close⟩ := rootedComponentVertex_near_birth_skeleton rule classicalRule configuration coherent sourceSide scale scalePositive
        marks address opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative coefficientNonnegative
        radiusBounds age depth bound beyond vertex
      exact Set.mem_iUnion.mpr ⟨anchor, close⟩
    · refine Set.mem_iUnion.mpr ⟨retainedComponentPersistentEmbedding rule configuration coherent sourceSide depth age bound vertex, ?_⟩
      rw [← rootedComponentVertex_persistent rule classicalRule configuration coherent sourceSide scale scalePositive address.length
        values nonnegative positive childConvergence depth age bound vertex]
      exact Metric.mem_closedBall_self (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))
  have coverCompletion := closure_minimal coverVertices coverClosed
  rw [(rootedComponentVertex_dense rule classicalRule configuration coherent sourceSide scale scalePositive address.length
    values nonnegative positive childConvergence).closure_eq] at coverCompletion
  obtain ⟨anchor, close⟩ := Set.mem_iUnion.mp (coverCompletion (Set.mem_univ point))
  exact ⟨anchor, Metric.mem_closedBall.mp close⟩

end
end IGSIII.Geometry
