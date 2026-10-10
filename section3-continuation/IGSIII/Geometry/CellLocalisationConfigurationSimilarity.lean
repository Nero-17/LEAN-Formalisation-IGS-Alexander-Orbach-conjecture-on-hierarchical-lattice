import IGSIII.Geometry.CellLocalisationScaledCompletion

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- Exact configuration equality transports each original finite vertex with
its original label; only the reachability proof changes. -/
def retainedComponentVertexConfigurationEquiv (rule : Rule)
    (firstConfiguration lastConfiguration : ∀ depth, Configuration (rule.generation depth).edges)
    (configurationEquality : firstConfiguration = lastConfiguration) (sourceSide : Bool) (depth : ℕ) :
    RetainedComponentVertex (rule.generation depth).network (firstConfiguration depth) sourceSide ≃
      RetainedComponentVertex (rule.generation depth).network (lastConfiguration depth) sourceSide := by
  cases configurationEquality
  exact Equiv.refl _
variable (rule : Rule) (classicalRule : rule.Classical)
variable (firstConfiguration lastConfiguration : ∀ depth, Configuration (rule.generation depth).edges)
variable (firstCoherent : configurationSequenceCoherent rule firstConfiguration)
variable (lastCoherent : configurationSequenceCoherent rule lastConfiguration) (sourceSide : Bool)
variable (scale : ℝ) (scalePositive : 0 < scale) (firstOffset lastOffset : ℕ)
variable (firstValues lastValues : ∀ fine, Fin (rule.generation fine).edges → ℝ)
variable (firstNonnegative : ∀ fine edge, 0 ≤ firstValues fine edge)
variable (firstPositive : ∀ fine edge, firstConfiguration fine edge = true → 0 < firstValues fine edge)
variable (lastNonnegative : ∀ fine edge, 0 ≤ lastValues fine edge)
variable (lastPositive : ∀ fine edge, lastConfiguration fine edge = true → 0 < lastValues fine edge)
variable (firstConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (firstConfiguration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + firstOffset)) atTop (𝓝 (firstValues coarse edge)))
variable (lastConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (lastConfiguration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2 + lastOffset)) atTop (𝓝 (lastValues coarse edge)))
variable (configurationEquality : firstConfiguration = lastConfiguration)
variable (factor : ℝ) (factorPositive : 0 < factor)
variable (valuesScaled : ∀ fine edge, lastValues fine edge = factor * firstValues fine edge)

/-- The completion similarity respects an exact relabelling of the same
actual configuration tower; no new randomness or abstract metric is inserted. -/
def rootedComponentCompletionSimilarityOfConfiguration :
    RootedComponentSpace rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive firstOffset
      firstValues firstNonnegative firstPositive firstConvergence ≃ᵤ
    RootedComponentSpace rule classicalRule lastConfiguration lastCoherent sourceSide scale scalePositive lastOffset
      lastValues lastNonnegative lastPositive lastConvergence := by
  cases configurationEquality
  exact rootedComponentCompletionSimilarity rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive
    firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence
    factor factorPositive valuesScaled

theorem rootedComponentCompletionSimilarityOfConfiguration_distance
    (first last : RootedComponentSpace rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive firstOffset
      firstValues firstNonnegative firstPositive firstConvergence) :
    dist (rootedComponentCompletionSimilarityOfConfiguration rule classicalRule firstConfiguration lastConfiguration firstCoherent lastCoherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence configurationEquality factor factorPositive valuesScaled first)
      (rootedComponentCompletionSimilarityOfConfiguration rule classicalRule firstConfiguration lastConfiguration firstCoherent lastCoherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence configurationEquality factor factorPositive valuesScaled last) = factor * dist first last := by
  cases configurationEquality
  exact rootedComponentCompletionSimilarity_distance rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive
    firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence
    factor factorPositive valuesScaled first last

theorem rootedComponentCompletionSimilarityOfConfiguration_vertex (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (firstConfiguration depth) sourceSide) :
    rootedComponentCompletionSimilarityOfConfiguration rule classicalRule firstConfiguration lastConfiguration firstCoherent lastCoherent sourceSide scale scalePositive firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence configurationEquality factor factorPositive valuesScaled
      (rootedComponentVertex rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive firstOffset
        firstValues firstNonnegative firstPositive firstConvergence depth vertex) =
    rootedComponentVertex rule classicalRule lastConfiguration lastCoherent sourceSide scale scalePositive lastOffset
      lastValues lastNonnegative lastPositive lastConvergence depth
      (retainedComponentVertexConfigurationEquiv rule firstConfiguration lastConfiguration configurationEquality sourceSide depth vertex) := by
  cases configurationEquality
  exact rootedComponentCompletionSimilarity_vertex rule classicalRule firstConfiguration firstCoherent sourceSide scale scalePositive
    firstOffset lastOffset firstValues lastValues firstNonnegative firstPositive lastNonnegative lastPositive firstConvergence lastConvergence
    factor factorPositive valuesScaled depth vertex
end
end IGSIII.Geometry

