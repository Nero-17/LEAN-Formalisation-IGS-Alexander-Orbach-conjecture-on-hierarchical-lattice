import IGSIII34.Diffusion.ActualElectricalComponentZeroRestriction
import IGSIII.Geometry.RootedComponentInclusion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)

include live in
theorem actualElectricalComponentConfiguration_block (fine : ℕ) :
    actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine =
      generationBlockCells rule coarse fine (stationaryConfiguration rule marks.val (coarse + fine + 1))
        (generationWordEdge rule coarse (fun index => (word index).1)) := by
  rw [actualElectricalComponentConfiguration_chosen rule p positive belowOne fixedPoint growth value marks coarse word live fine]
  exact (generationBlockCells_marked rule marks.val coarse fine [] true _).symm

/-- Original component labels are retained unchanged by the exact
configuration transport from address coordinates to block coordinates. -/
def actualElectricalComponentBlockVertex (fine : ℕ) :
    RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected ≃
    RetainedComponentVertex (rule.generation fine).network
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks.val (coarse + fine + 1))
        (generationWordEdge rule coarse (fun index => (word index).1)))
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected :=
  Equiv.subtypeEquivRight (fun vertex => by
    rw [actualElectricalComponentConfiguration_block rule p positive belowOne fixedPoint growth value marks coarse word live fine])

theorem actualElectricalComponentBlockVertex_val (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) :
    (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live fine vertex).val = vertex.val := rfl

/-- The constructed electrical completion inclusion has the same original
block birth coordinates as the canonical chemical cell inclusion. -/
theorem actualElectricalComponentFiniteInclusion_block_birth (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) :
    actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live fine vertex =
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) (coarse + fine + 1)
      (retainedBlockComponentEmbedding rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
          (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks)) coarse fine
        (generationWordEdge rule coarse (fun index => (word index).1))
        (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
        (actualElectricalComponent_chosen_anchor_retained rule p positive belowOne fixedPoint growth value marks coarse word live)
        (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live fine vertex)) := by
  have indexIdentity : fine + (componentEdgeAddress (List.ofFn word)).length = coarse + fine + 1 := by
    simp only [componentEdgeAddress, List.length_map, List.length_ofFn]
    omega
  unfold actualElectricalComponentFiniteInclusion
  rw [actualStationaryElectricalVertex_index rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) _ _ indexIdentity]
  apply congrArg
  apply Subtype.ext
  rw [retainedSkeletonVertexAtIndex_val]
  have birthIdentity := generationAddressEmbedding_block_vertex rule coarse fine (fun index => (word index).1)
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine) vertex.val vertex.property
  rw [generationEmbeddingAtIndex_vertex] at birthIdentity
  change Fin.cast (congrArg (fun depth => (rule.generation depth).vertices) indexIdentity)
      ((generationAddressEmbedding rule (componentEdgeAddress (List.ofFn word)) fine).vertex vertex.val) =
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse (fun index => (word index).1))).vertex vertex.val
  apply Fin.ext
  simp only [Fin.val_cast]
  have addressIdentity : componentEdgeAddress (List.ofFn word) = List.ofFn (fun index => (word index).1) := by
    simp only [componentEdgeAddress, List.map_ofFn, Function.comp_def]
  rw [addressIdentity]
  simpa only [Fin.val_cast] using congrArg Fin.val birthIdentity

end
end IGSIII34.ResistanceLimit
