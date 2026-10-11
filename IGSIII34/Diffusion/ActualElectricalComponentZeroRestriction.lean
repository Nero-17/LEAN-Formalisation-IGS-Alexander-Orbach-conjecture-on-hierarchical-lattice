import IGSIII34.Diffusion.ActualElectricalComponentZeroStages
import IGSIII34.Diffusion.ActualComponentBirthEmbeddingIdentity
import IGSIII34.Diffusion.ActualElectricalComponentRestriction
import IGSIII34.ResistanceLimit.StationaryBlockZeroSkeleton

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

def retainedSkeletonVertexAtIndex (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (first last : ℕ) (equal : first = last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    RetainedSkeletonVertex (rule.generation last).network (configuration last) := equal ▸ vertex

theorem retainedSkeletonVertexAtIndex_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (first last : ℕ) (equal : first = last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (configuration first)) :
    (retainedSkeletonVertexAtIndex rule configuration first last equal vertex).val =
      Fin.cast (congrArg (fun depth => (rule.generation depth).vertices) equal) vertex.val := by
  cases equal
  rfl

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualStationaryElectricalVertex_index
    (rootMarks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (first last : ℕ) (equal : first = last)
    (vertex : RetainedSkeletonVertex (rule.generation first).network (stationaryConfiguration rule rootMarks.val first)) :
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive rootMarks first vertex =
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive rootMarks last
        (retainedSkeletonVertexAtIndex rule (stationaryConfiguration rule rootMarks.val) first last equal vertex) := by
  cases equal
  rfl

variable (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)
  (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ)
  (boundaryZero : ∀ side : Bool, potential (rootedElectricalSkeletonPoint rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) 0
    (plantedVertex (rule.generation 0).network side)) = 0)

include boundaryZero in
/-- A continuous global realization of the actual zero tower restricts
exactly to its supplied intrinsic function on every local born vertex. -/
theorem actualElectricalComponent_zero_restriction_born
    (extension : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks), ℝ))
    (globalBorn : ∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network
      (stationaryConfiguration rule marks.val depth)),
      extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
      actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val)
    (fine : ℕ) (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) :
    extension (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live fine vertex) =
      potential (rootedElectricalSkeletonVertex rule
        (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
        (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) fine vertex) := by
  have indexIdentity : fine + (componentEdgeAddress (List.ofFn word)).length = coarse + fine + 1 := by
    simp only [componentEdgeAddress, List.length_map, List.length_ofFn]
    omega
  unfold actualElectricalComponentFiniteInclusion
  rw [actualStationaryElectricalVertex_index rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) _ _ indexIdentity]
  rw [globalBorn, retainedSkeletonVertexAtIndex_val]
  have birthIdentity := generationAddressEmbedding_block_vertex rule coarse fine (fun index => (word index).1)
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine) vertex.val vertex.property
  rw [generationEmbeddingAtIndex_vertex] at birthIdentity
  have bornVertex : Fin.cast (congrArg (fun depth => (rule.generation depth).vertices) indexIdentity)
      (actualElectricalComponentRetainedEmbedding rule p positive belowOne fixedPoint growth value marks (List.ofFn word) live fine vertex).val =
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse (fun index => (word index).1))).vertex vertex.val := by
    change Fin.cast (congrArg (fun depth => (rule.generation depth).vertices) indexIdentity)
      ((generationAddressEmbedding rule (componentEdgeAddress (List.ofFn word)) fine).vertex vertex.val) = _
    apply Fin.ext
    simp only [Fin.val_cast]
    have addressIdentity : componentEdgeAddress (List.ofFn word) = List.ofFn (fun index => (word index).1) := by
      simp only [componentEdgeAddress, List.map_ofFn, Function.comp_def]
    rw [addressIdentity]
    simpa only [Fin.val_cast] using congrArg Fin.val birthIdentity
  rw [bornVertex, actualBlockZeroTowerStage_tail, actualBlockZeroExtension_chosen rule coarse fine _ _
    (actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero true fine)
    (actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero false fine)]
  simp only [actualElectricalComponentStagePotential, rootedElectricalStagePotential, dif_pos vertex.property]
  rfl

include boundaryZero in
/-- The same zero tower has exactly the intended restriction on the entire
intrinsic completion, rather than merely on the original finite vertices. -/
theorem actualElectricalComponent_zero_completed_restriction
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential)
    (extension : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks), ℝ))
    (globalBorn : ∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network
      (stationaryConfiguration rule marks.val depth)),
      extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
      actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val)
    (point : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)) :
    extension (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live point) =
      actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential point :=
  actualElectricalComponent_completed_restriction_of_born rule p positive belowOne fixedPoint growth value growthPositive marks
    (List.ofFn word) live potential finite extension
    (actualElectricalComponent_zero_restriction_born rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live potential boundaryZero extension globalBorn) point

end
end IGSIII34.Diffusion
