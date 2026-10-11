import IGSIII34.ResistanceLimit.ActualChemicalCellBornClosure
import IGSIII34.ResistanceLimit.ElectricalComponentBlockBirth
import IGSIII34.Topology.CompletionInverseDistance

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Spectral IGSIII34.Topology MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalGrowth amplitude : ℝ) (chemicalGrowthPositive : 0 < chemicalGrowth) (amplitudePositive : 0 < amplitude)
  (chemicalValue : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (chemicalCoherent : configurationSequenceCoherent rule (stationaryConfiguration rule marks.val))
  (chemicalFieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint chemicalValue address marks.val)
  (chemicalFieldConvergence : ∀ address, Tendsto
    (fun depth => (markedTerminalDistance rule marks.val depth address true : ℝ) / chemicalGrowth ^ (depth + 1))
    atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint chemicalValue address marks.val)))

variable (homeomorph : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) ≃ₜ
    (let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalFieldPositive chemicalFieldConvergence
     ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val) chemicalCoherent
       chemicalGrowth chemicalGrowthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks.val)
       data.1 data.2.1 data.2.2))
  (birth : ∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)),
    homeomorph (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
    let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalFieldPositive chemicalFieldConvergence
    actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val) chemicalCoherent
      chemicalGrowth chemicalGrowthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks.val)
      data.1 data.2.1 data.2.2 depth vertex)
  (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)

include birth in
/-- The electrical intrinsic completion has exactly the canonical closed
chemical cell as its image in the same global carrier. Closedness is the
inverse metric estimate supplied by the actual finite electrical network. -/
theorem actualElectricalComponent_chemical_cell_range
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks.val depth descendant state : ℝ) /
        chemicalGrowth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (closed : IsClosed (Set.range (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live))) :
    Set.range (fun point => homeomorph (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live point)) =
    actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
      chemicalFieldPositive chemicalFieldConvergence coarse word := by
  let electricalBorn := fun point : Σ fine, RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected =>
    rootedElectricalVertex rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) point.1 point.2
  let chemicalBorn := fun point : Σ fine, RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected =>
    actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalGrowthPositive amplitudePositive
      chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence coarse
      (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      point.1 (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live point.1 point.2)
  have electricalDense : DenseRange electricalBorn := by
    apply (rootedElectricalVertex_dense rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word))).mono
    rintro point member
    obtain ⟨fine, vertex, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨⟨fine, vertex⟩, rfl⟩
  have chemicalDense : DenseRange chemicalBorn := by
    apply (actualChemicalCellVertex_dense rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalGrowthPositive amplitudePositive
      chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence coarse
      (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected).mono
    rintro point ⟨⟨fine, vertex⟩, rfl⟩
    obtain ⟨preimage, equal⟩ := (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live fine).surjective vertex
    exact ⟨⟨fine, preimage⟩, congrArg (actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
      coarse (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected fine) equal⟩
  unfold actualChemicalWordComponent
  rw [dif_pos live]
  apply closed_ranges_eq_of_dense_agreement electricalBorn electricalDense chemicalBorn chemicalDense
    (fun point => homeomorph (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live point))
    (homeomorph.continuous.comp (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live).continuous)
    _ (actualChemicalCellInclusion_isClosedEmbedding rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds coarse
      (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected _).continuous
  · rw [Set.range_comp']
    exact homeomorph.isClosedMap _ closed
  · exact (actualChemicalCellInclusion_isClosedEmbedding rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds coarse
      (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected _).isClosed_range
  · intro point
    dsimp only [electricalBorn, chemicalBorn]
    erw [actualElectricalComponentCompletionInclusion_born, actualElectricalComponentFiniteInclusion_block_birth,
      birth, actualChemicalCellInclusion_born]
    rfl

end
end IGSIII34.ResistanceLimit
