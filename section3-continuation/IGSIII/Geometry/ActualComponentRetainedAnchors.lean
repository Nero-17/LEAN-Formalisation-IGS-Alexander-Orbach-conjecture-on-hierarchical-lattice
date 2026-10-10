import IGSIII.Geometry.ActualComponentBoundary
import IGSIII.Geometry.ActualFiniteMass

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

def actualComponentRetainedAnchor (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (age : ℕ) (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    RetainedSkeletonVertex (rule.generation age).network (markedGenerationConfiguration rule marks age [] true) :=
  if live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive then
    ⟨componentWordAnchor rule marks age word, componentWordAnchor_retained rule marks crossing age word live⟩
  else ⟨(rule.generation age).network.source, SimpleGraph.Reachable.refl _⟩

variable (rule : Rule) (classicalRule : rule.Classical)
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
variable (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
variable (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < limitLength depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))

theorem actualComponentWordPoint_eq_retained_anchor (age : ℕ)
    (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    actualComponentWordPoint rule classicalRule marks crossing coherent scale scalePositive
      limitLength nonnegative positive childConvergence age word =
      actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive limitLength nonnegative positive childConvergence age
          (actualComponentRetainedAnchor rule marks crossing age word) := by
  by_cases live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive
  · simp only [actualComponentWordPoint, actualComponentRetainedAnchor, dif_pos live]
  · simp only [actualComponentWordPoint, actualComponentRetainedAnchor, dif_neg live]
    have persistence := actualChemicalVertex_persistent rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive
      limitLength nonnegative positive childConvergence 0 age (Nat.zero_le _)
      ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩
    have sourceEquality : retainedPersistentVertexEmbedding rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent 0 age (Nat.zero_le _)
        ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩ =
        ⟨(rule.generation age).network.source, SimpleGraph.Reachable.refl _⟩ := by
      apply Subtype.ext
      exact persistentVertexEmbedding_planted rule 0 age (Nat.zero_le _) true
    rw [sourceEquality] at persistence
    exact persistence

end
end IGSIII.Geometry
