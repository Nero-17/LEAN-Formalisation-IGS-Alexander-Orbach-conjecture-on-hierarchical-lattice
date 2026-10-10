import IGSIII.Geometry.RootedComponentPersistence
import IGSIII.Geometry.CellLocalisationSimilarity

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
variable (firstOffset lastOffset : ℕ)
variable (firstValues lastValues : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (firstNonnegative : ∀ fine edge, 0 ≤ firstValues fine edge)
variable (firstPositive : ∀ fine edge, configuration fine edge = true → 0 < firstValues fine edge)
variable (lastNonnegative : ∀ fine edge, 0 ≤ lastValues fine edge)
variable (lastPositive : ∀ fine edge, configuration fine edge = true → 0 < lastValues fine edge)
variable (firstConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + firstOffset)) atTop (𝓝 (firstValues coarse edge)))
variable (lastConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + lastOffset)) atTop (𝓝 (lastValues coarse edge)))
variable (factor : ℝ) (factorPositive : 0 < factor)
variable (valuesScaled : ∀ fine edge, lastValues fine edge = factor * firstValues fine edge)
/-- The two differently scaled directed skeletons have the same genuine
persistent-vertex labels and the same equivalence relation. -/
def rootedComponentSkeletonScalingEquiv : RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence ≃ RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence := Equiv.refl _

include valuesScaled factorPositive in
theorem rootedComponentSkeletonScalingEquiv_distance
    (first last : RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence) :
    dist (rootedComponentSkeletonScalingEquiv rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence first) (rootedComponentSkeletonScalingEquiv rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence last) = factor * dist first last := by
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun fine => RetainedComponentVertex (rule.generation fine).network (configuration fine) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) (fun fine first last => ?_) first last
  have firstDistance : @dist (RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence) (rootedComponentSkeletonMetricSpace rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence).toPseudoMetricSpace.toDist ⟦⟨fine, first⟩⟧ ⟦⟨fine, last⟩⟧ =
      weightedDistance ((rule.generation fine).network.openGraph (configuration fine))
        (indexedBondCost (rule.generation fine).network (firstValues fine)) first.val last.val := by
    letI (depth : ℕ) := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
      (configuration depth) sourceSide (firstValues depth) (firstNonnegative depth) (firstPositive depth)
    exact Universality.Geometry.MetricDirectLimit.compatibleDistance_mk
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (Universality.Geometry.IsometricSequence.transition _ (retainedComponentOldEmbedding rule configuration coherent sourceSide))
      (Universality.Geometry.IsometricSequence.transition_isometry _ _ (retainedComponentOldEmbedding_isometry rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence)) fine first last
  have lastDistance : @dist (RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence) (rootedComponentSkeletonMetricSpace rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence).toPseudoMetricSpace.toDist ⟦⟨fine, first⟩⟧ ⟦⟨fine, last⟩⟧ =
      weightedDistance ((rule.generation fine).network.openGraph (configuration fine))
        (indexedBondCost (rule.generation fine).network (lastValues fine)) first.val last.val := by
    letI (depth : ℕ) := retainedComponentMetric (rule.generation depth).network (classicalRule.generation depth).simple
      (configuration depth) sourceSide (lastValues depth) (lastNonnegative depth) (lastPositive depth)
    exact Universality.Geometry.MetricDirectLimit.compatibleDistance_mk
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (Universality.Geometry.IsometricSequence.transition _ (retainedComponentOldEmbedding rule configuration coherent sourceSide))
      (Universality.Geometry.IsometricSequence.transition_isometry _ _ (retainedComponentOldEmbedding_isometry rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence)) fine first last
  change @dist (RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence) (rootedComponentSkeletonMetricSpace rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence).toPseudoMetricSpace.toDist ⟦⟨fine, first⟩⟧ ⟦⟨fine, last⟩⟧ =
    factor * @dist (RootedComponentSkeleton rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence) (rootedComponentSkeletonMetricSpace rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence).toPseudoMetricSpace.toDist ⟦⟨fine, first⟩⟧ ⟦⟨fine, last⟩⟧
  rw [lastDistance, firstDistance]
  have lengthsIdentity : lastValues fine = fun edge => factor * firstValues fine edge := funext (valuesScaled fine)
  rw [lengthsIdentity, indexedBondCost_scale, weightedDistance_scale _ _ factor factorPositive.le]

/-- Scaling the actual leaf lengths induces a canonical similarity of the
entire intrinsic completions, extending the same persistent finite vertices. -/
def rootedComponentCompletionSimilarity : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence ≃ᵤ RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence :=
  completionSimilarity (rootedComponentSkeletonScalingEquiv rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence) factor factorPositive
    (rootedComponentSkeletonScalingEquiv_distance rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence factor factorPositive valuesScaled)

theorem rootedComponentCompletionSimilarity_distance
    (first last : RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence) :
    dist (rootedComponentCompletionSimilarity rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence factor factorPositive valuesScaled first)
      (rootedComponentCompletionSimilarity rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence factor factorPositive valuesScaled last) = factor * dist first last :=
  completionSimilarity_distance _ factor factorPositive _ first last

theorem rootedComponentCompletionSimilarity_vertex (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network (configuration fine) sourceSide) :
    rootedComponentCompletionSimilarity rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence factor factorPositive valuesScaled (rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive firstOffset firstValues firstNonnegative firstPositive firstConvergence fine vertex) =
      rootedComponentVertex rule classicalRule configuration coherent sourceSide scale scalePositive lastOffset lastValues lastNonnegative lastPositive lastConvergence fine vertex := by
  exact completionSimilarity_coe _ _ _ _ _

end
end IGSIII.Geometry




