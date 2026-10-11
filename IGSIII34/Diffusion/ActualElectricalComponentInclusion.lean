import IGSIII34.Diffusion.ActualElectricalComponentFiniteInclusion
import IGSIII34.Diffusion.RootedElectricalStagePotential
import IGSIII34.ResistanceLimit.ElectricalPersistence
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : MeasureTheory.Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (word : List (Fin rule.edges × Bool))
  (live : retainedComponentState rule marks.val word ≠ .inactive)

theorem actualElectricalComponentFiniteInclusion_transition (first second : ℕ) (bound : first ≤ second)
    (vertex : RetainedComponentVertex (rule.generation first).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word first)
      (retainedComponentState rule marks.val word).sourceSelected) :
    actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live first vertex =
    actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live second
      (Universality.Geometry.IsometricSequence.transition (fun depth => RetainedComponentVertex (rule.generation depth).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth)
      (retainedComponentState rule marks.val word).sourceSelected) (retainedComponentOldEmbedding rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected) first second bound vertex) := by
  simp only [actualElectricalComponentFiniteInclusion, actualStationaryElectricalVertex, componentTypicalRootElectricalMarks]
  rw [electricalVertex_persistent rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (fun depth first last reachable => marks.property.2.2 depth [] true first last reachable)
    (first + (componentEdgeAddress word).length) (second + (componentEdgeAddress word).length) (by omega)]
  apply congrArg (electricalVertex rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (fun depth first last reachable => marks.property.2.2 depth [] true first last reachable) (second + (componentEdgeAddress word).length))
  apply Subtype.ext
  change persistentVertexEmbedding rule (first + (componentEdgeAddress word).length) (second + (componentEdgeAddress word).length) (by omega)
    ((generationAddressEmbedding rule (componentEdgeAddress word) first).vertex vertex.val) = _
  rw [generationAddressEmbedding_persistent rule (componentEdgeAddress word) first second bound vertex.val]
  change _ = (generationAddressEmbedding rule (componentEdgeAddress word) second).vertex _
  rw [retainedComponentTransition_val]

/-- The original finite birth embeddings descend to the true intrinsic
component skeleton, before completing it. -/
def actualElectricalComponentSkeletonInclusion :
    ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks word →
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) :=
  DirectLimit.lift (Universality.Geometry.IsometricSequence.transition (fun depth => RetainedComponentVertex (rule.generation depth).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth)
      (retainedComponentState rule marks.val word).sourceSelected) (retainedComponentOldEmbedding rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected))
    (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live)
    (actualElectricalComponentFiniteInclusion_transition rule p positive belowOne fixedPoint growth value growthPositive marks word live)

theorem actualElectricalComponentSkeletonInclusion_mk (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected) :
    actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live
      (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine vertex) =
    actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live fine vertex := rfl

theorem actualElectricalComponentSkeletonInclusion_lipschitz :
    LipschitzWith (Real.toNNReal (growth⁻¹ ^ (componentEdgeAddress word).length))
      (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  refine DirectLimit.induction₂ (Universality.Geometry.IsometricSequence.transition (fun depth => RetainedComponentVertex (rule.generation depth).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word depth)
      (retainedComponentState rule marks.val word).sourceSelected) (retainedComponentOldEmbedding rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected))
    (fun fine first last => ?_) first last
  change dist (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live
      (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine first))
    (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live
      (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine last)) ≤
    (Real.toNNReal (growth⁻¹ ^ (componentEdgeAddress word).length) : ℝ) *
    dist (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine first)
      (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine last)
  rw [actualElectricalComponentSkeletonInclusion_mk, actualElectricalComponentSkeletonInclusion_mk,
    rootedElectricalSkeletonVertex_distance, Real.coe_toNNReal _ (pow_nonneg (inv_nonneg.mpr growthPositive.le) _)]
  exact actualElectricalComponentFiniteInclusion_resistance_le rule p positive belowOne fixedPoint growth value growthPositive marks word live fine first last

/-- A genuine Lipschitz inclusion from the intrinsic completion into the
same original global electrical carrier, constructed by completion extension. -/
def actualElectricalComponentCompletionInclusion :
    ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word →
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) :=
  UniformSpace.Completion.extension
    (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live)

theorem actualElectricalComponentCompletionInclusion_lipschitz :
    LipschitzWith (Real.toNNReal (growth⁻¹ ^ (componentEdgeAddress word).length))
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live) :=
  (actualElectricalComponentSkeletonInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks word live).completion_extension

/-- On every genuine born component vertex, the completed inclusion is
exactly the original finite address embedding in the SAME global carrier. -/
theorem actualElectricalComponentCompletionInclusion_born (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected) :
    actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live
      (UniformSpace.Completion.coe' (rootedElectricalSkeletonVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
      (retainedComponentState rule marks.val word).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word) fine vertex)) =
    actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live fine vertex := by
  rw [actualElectricalComponentCompletionInclusion, UniformSpace.Completion.extension_coe
    (actualElectricalComponentSkeletonInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks word live).uniformContinuous]
  exact actualElectricalComponentSkeletonInclusion_mk rule p positive belowOne fixedPoint growth value growthPositive marks word live fine vertex

end
end IGSIII34.Diffusion
