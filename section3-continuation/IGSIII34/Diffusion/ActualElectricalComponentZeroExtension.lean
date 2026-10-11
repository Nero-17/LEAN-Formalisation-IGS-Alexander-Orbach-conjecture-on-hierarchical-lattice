import IGSIII34.Diffusion.ActualElectricalComponentZeroRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})

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

include live in
theorem actualElectricalComponent_chosen_trace_energy (fine : ℕ) :
    sourceComponentEnergy
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
  rw [← actualElectricalComponentConfiguration_chosen rule p positive belowOne fixedPoint growth value marks coarse word live fine]
  have addressIdentity : generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1)) =
      componentEdgeAddress (List.ofFn word) := by
    simp only [generationWordEdge_address, componentEdgeAddress, List.map_ofFn, Function.comp_def]
  rw [addressIdentity]
  exact rootedElectricalStagePotential_energy rule _ _ _ _ _ _ potential fine

include live boundaryZero in
/-- Every actual intrinsic finite-energy function vanishing at its planted
boundary extends into the SAME global completed form, with exact energy and
its intended restriction on every point of the intrinsic completion. -/
theorem actualElectricalComponent_completed_zero_extension
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential) :
    let rootMarks := componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks
    let endpoint := skeletonEnergyEndpoint rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value rootMarks)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive rootMarks)
      rootMarks.property.2.2
    let conductance := skeletonEnergyConductance rule (stationaryConfiguration rule marks.val)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    let nonnegative := skeletonEnergyConductance_nonnegative rule (stationaryConfiguration rule marks.val)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive rootMarks)
    ∃ extension : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive rootMarks, ℝ),
      (extension : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive rootMarks → ℝ) ∈
        energyDomain (completionEnergyEndpoint endpoint) conductance nonnegative ∧
      limitingEnergy (completionEnergyEndpoint endpoint) conductance extension =
        growth ^ (coarse + 1) * actualElectricalComponentIntrinsicEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential ∧
      (∀ point : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word),
        extension (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live point) =
          actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential point) ∧
      (∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)),
        extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive rootMarks depth vertex) =
          actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
            (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val) := by
  dsimp only
  have configurationIdentity := actualElectricalComponentConfiguration_chosen rule p positive belowOne fixedPoint growth value marks coarse word live
  have atSource := fun fine => actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero true fine
  have atTarget := fun fine => actualElectricalComponentStagePotential_boundary_zero rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential boundaryZero false fine
  have restriction := fun fine vertex => rootedElectricalStagePotential_old rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) potential fine vertex
  obtain ⟨extension, atSkeleton, domain, energy⟩ := stationary_block_zero_completion_extension rule marks.val marks.property.2.1
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    growth growthPositive marks.property.1 stationary
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks))
    (fun depth first last reachable => marks.property.2.2 depth [] true first last reachable)
    coarse (generationWordEdge rule coarse (fun index => (word index).1))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential)
    (fun fine => by rw [← configurationIdentity fine]; exact rootedElectricalStagePotential_projection rule _ _ _ _ _ _ potential fine)
    atSource atTarget restriction
    (actualElectricalComponent_chosen_anchor_retained rule p positive belowOne fixedPoint growth value marks coarse word live)
    (by
      simp_rw [actualElectricalComponent_chosen_trace_energy rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live potential]
      exact finite)
  have globalBorn (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
      extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
      actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val := by
    change extension (UniformSpace.Completion.coe' (electricalSkeletonVertex rule _ _ _ _ _ depth vertex)) = _
    rw [atSkeleton]
    exact stationaryBlockZeroSkeletonPotential_retained rule marks.val _ growth growthPositive marks.property.1 _ _
      coarse _ _ atSource atTarget restriction depth vertex
  refine ⟨extension, domain, ?_, ?_, globalBorn⟩
  · simp_rw [actualElectricalComponent_chosen_trace_energy rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live potential] at energy
    exact energy
  · exact actualElectricalComponent_zero_completed_restriction rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live potential boundaryZero finite extension globalBorn

end
end IGSIII34.Diffusion

