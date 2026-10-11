import IGSIII34.Spectral.Collars.ActualFiniteOriginalJointResponseTransport
import IGSIII34.ResistanceLimit.ActualSameCarrierMeasuredMarkedState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory TopologicalSpace

theorem jointMeasuredMarkedStateMap_fullState_range
    {Source Ambient : Type} [MetricSpace Source] [CompactSpace Source] [Nonempty Source]
    [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (marks : Bool → Source) (masses : Bool → ProbabilityMeasure Source)
    (placement : Source → Ambient) (continuous : Continuous placement) :
    jointMeasuredMarkedStateMap placement continuous (originalJointCompactFullState marks masses) =
      (continuousNonemptyCompactRange placement continuous, placement ∘ marks,
        fun side => (masses side).map continuous.measurable.aemeasurable) := by
  apply Prod.ext
  · apply NonemptyCompacts.ext
    change placement '' Set.univ = Set.range placement
    exact Set.image_univ
  · rfl

theorem actualFullConfigurationMass_eq_bothProbability
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (counting : Bool) :
    actualFullConfigurationMass rule configuration scale scalePositive depth (crossing depth) counting =
      actualBothFiniteClusterProbability rule configuration crossing scale scalePositive depth counting := by
  apply ProbabilityMeasure.toMeasure_injective
  cases counting <;> rfl

theorem actualFullConfigurationFullState_placed
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    {Ambient : Type} [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (placement : ActualFiniteCluster rule configuration scale scalePositive depth → Ambient)
    (continuous : Continuous placement) :
    jointMeasuredMarkedStateMap placement continuous
      (originalJointCompactFullState
        (actualFullConfigurationMark rule configuration scale scalePositive depth (crossing depth))
        (actualFullConfigurationMass rule configuration scale scalePositive depth (crossing depth))) =
      (continuousNonemptyCompactRange placement continuous,
        fun side => placement (IGSIII.Chemical.SmallBall.actualFiniteClusterTerminal
          rule configuration crossing scale scalePositive depth side),
        fun counting => (actualBothFiniteClusterProbability rule configuration crossing
          scale scalePositive depth counting).map (measurable_of_finite placement).aemeasurable) := by
  rw [jointMeasuredMarkedStateMap_fullState_range]
  apply Prod.ext rfl
  apply Prod.ext
  · funext side
    exact congrArg placement (actualFullConfigurationMark_terminal
      rule configuration scale scalePositive depth crossing side)
  · funext counting
    rfl

end
end IGSIII34.Spectral
