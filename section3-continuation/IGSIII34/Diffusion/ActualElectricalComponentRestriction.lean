import IGSIII34.Diffusion.ActualElectricalComponentInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (word : List (Fin rule.edges × Bool))
  (live : retainedComponentState rule marks.val word ≠ .inactive)

/-- Exact restriction at every genuine born vertex determines the whole
intrinsic completed restriction. This uses the constructed original map. -/
theorem actualElectricalComponent_completed_restriction_of_born
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word → ℝ)
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks word potential)
    (extension : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks), ℝ))
    (born : ∀ fine (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected),
      extension (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live fine vertex) =
        potential (rootedElectricalSkeletonVertex rule
          (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
          (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
          (retainedComponentState rule marks.val word).sourceSelected
          (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
          (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
          (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine vertex))
    (point : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word) :
    extension (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live point) =
      actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks word potential point := by
  refine UniformSpace.Completion.induction_on point
    (isClosed_eq (extension.continuous.comp
      (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks word live).continuous)
      (actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks word potential).continuous) ?_
  intro skeleton
  refine DirectLimit.induction (Universality.Geometry.IsometricSequence.transition
    (fun depth => RetainedComponentVertex (rule.generation depth).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth)
      (retainedComponentState rule marks.val word).sourceSelected)
    (retainedComponentOldEmbedding rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected)) (fun fine vertex => ?_) skeleton
  change extension (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live
    (UniformSpace.Completion.coe' (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine vertex))) = _
  rw [actualElectricalComponentCompletionInclusion_born]
  exact (born fine vertex).trans
    (rootedElectricalIntrinsicCompletionExtension_coe rule _ _ _ _ _ _ potential finite
      (rootedElectricalSkeletonVertex rule
        (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
        (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
        (retainedComponentState rule marks.val word).sourceSelected
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
        (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
        (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine vertex)).symm

end
end IGSIII34.Diffusion
