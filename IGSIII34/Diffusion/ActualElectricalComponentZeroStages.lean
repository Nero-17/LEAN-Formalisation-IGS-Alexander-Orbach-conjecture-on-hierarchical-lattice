import IGSIII34.Diffusion.ActualElectricalComponentCompletion
import IGSIII34.Diffusion.RootedElectricalBoundaryStages
import IGSIII34.ResistanceLimit.StationaryBlockZeroLimit
import IGSIII.Geometry.ComponentWordAnchors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)

/-- The supplied stages of an actual intrinsic component function, with
zero values outside its retained planted side. -/
def actualElectricalComponentStagePotential
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ)
    (fine : ℕ) : Fin (rule.generation fine).vertices → ℝ :=
  rootedElectricalStagePotential rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) potential fine

include live in
theorem actualElectricalComponentConfiguration_chosen (fine : ℕ) :
    actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine =
      markedGenerationConfiguration rule marks.val fine
        (generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1)))
        (markedGenerationConfiguration rule marks.val coarse [] true
          (generationWordEdge rule coarse (fun index => (word index).1))) := by
  have bitIdentity : markedGenerationConfiguration rule marks.val coarse [] true
      (generationWordEdge rule coarse (fun index => (word index).1)) =
      (retainedComponentState rule marks.val (List.ofFn word)).massOpened := by
    simpa [OrientedState.massOpened, retainedComponentState] using
      generationWordEdge_massOpened rule marks.val coarse [] .connected word live
  rw [generationWordEdge_address, bitIdentity]
  simp only [actualElectricalComponentConfiguration, componentEdgeAddress, List.map_ofFn, Function.comp_def]

include live in
theorem actualElectricalComponent_chosen_anchor_retained :
    ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks.val coarse [] true)).Reachable
      (rule.generation coarse).network.source
      (coarseCellPlantedVertex rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) := by
  exact componentWordAnchor_retained rule marks.val marks.property.2.1 coarse word live

variable (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ)
variable (boundaryZero : ∀ side : Bool, potential (rootedElectricalSkeletonPoint rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) 0
    (plantedVertex (rule.generation 0).network side)) = 0)

include boundaryZero in
theorem actualElectricalComponentStagePotential_boundary_zero (side : Bool) (fine : ℕ) :
    actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential fine
      (plantedVertex (rule.generation fine).network side) = 0 :=
  rootedElectricalStagePotential_boundary_zero rule _ _ _ _ _ _ potential side (boundaryZero side) fine

include live boundaryZero in
/-- An arbitrary intrinsic finite-energy function with zero planted boundary
supplies the actual global coherent zero tower, with exact global scaling. -/
theorem actualElectricalComponent_zero_tower_energy
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential) :
    BddAbove (Set.range (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks.val depth [] true))
      (fun edge => stationaryGenerationResistance rule
        (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth depth [] edge.val)
      (actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth))) ∧
    (⨆ depth, sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks.val depth [] true))
      (fun edge => stationaryGenerationResistance rule
        (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth depth [] edge.val)
      (actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth)) =
      growth ^ (coarse + 1) * actualElectricalComponentIntrinsicEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential := by
  have configurationIdentity := actualElectricalComponentConfiguration_chosen rule p positive belowOne fixedPoint growth value marks coarse word live
  have addressIdentity : generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1)) =
      componentEdgeAddress (List.ofFn word) := by
    simp only [generationWordEdge_address, componentEdgeAddress, List.map_ofFn, Function.comp_def]
  have traceIdentity (fine : ℕ) : sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks.val fine
          (generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1)))
          (markedGenerationConfiguration rule marks.val coarse [] true
            (generationWordEdge rule coarse (fun index => (word index).1)))))
        (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected)
      (fun edge => stationaryGenerationResistance rule
        (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth fine
          (generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1))) edge.val)
      (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential fine) =
      rootedElectricalIntrinsicTraceEnergy rule
        (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
        (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
        (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) fine potential := by
    rw [← configurationIdentity fine]
    rw [addressIdentity]
    exact rootedElectricalStagePotential_energy rule _ _ _ _ _ _ potential fine
  have result := stationary_block_zero_extension_limit rule marks.val marks.property.2.1
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    growth growthPositive marks.property.1 stationary coarse
    (generationWordEdge rule coarse (fun index => (word index).1))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential)
    (fun fine => by
      rw [← configurationIdentity fine]
      exact rootedElectricalStagePotential_projection rule _ _ _ _ _ _ potential fine)
    (fun fine => actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero true fine)
    (fun fine => actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero false fine)
    (fun fine vertex => rootedElectricalStagePotential_old rule _ _ _ _ _ _ potential fine vertex)
    (actualElectricalComponent_chosen_anchor_retained rule p positive belowOne fixedPoint growth value marks coarse word live)
    (by
      simp_rw [traceIdentity]
      exact finite)
  refine ⟨result.1, ?_⟩
  convert result.2 using 1
  congr 1
  simp only [actualElectricalComponentIntrinsicEnergy, rootedElectricalIntrinsicEnergy]
  simp_rw [traceIdentity]

end
end IGSIII34.Diffusion
