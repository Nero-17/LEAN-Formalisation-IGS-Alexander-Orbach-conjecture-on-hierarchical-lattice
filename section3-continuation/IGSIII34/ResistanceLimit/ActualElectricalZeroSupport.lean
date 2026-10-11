import IGSIII34.ResistanceLimit.ActualElectricalChemicalCellRange
import IGSIII34.ResistanceLimit.BlockZeroSupport
import IGSIII34.ResistanceLimit.CompletionCellZeroSupport
import IGSIII34.Diffusion.ActualElectricalComponentZeroExtension

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


include birth live in
/-- The constructed zero tower vanishes everywhere outside the canonical
closed physical cell, including points not on the original skeleton. -/
theorem actualElectricalComponent_zero_outside_chemical_cell
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks.val depth descendant state : ℝ) /
        chemicalGrowth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ)
    (extension : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks), ℝ))
    (globalBorn : ∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)),
      extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
      actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
        (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val) :
    ∀ point, homeomorph point ∉ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
      chemicalFieldPositive chemicalFieldConvergence coarse word → extension point = 0 := by
  let born := fun point : Σ depth, RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth) =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) point.1 point.2
  have dense : DenseRange born := by
    apply (actualStationaryElectricalVertex_dense rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks)).mono
    rintro point member
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨⟨depth, vertex⟩, rfl⟩
  let cell := actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
    chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
    chemicalFieldPositive chemicalFieldConvergence coarse word
  have closed : IsClosed (homeomorph ⁻¹' cell) :=
    (actualChemicalWordComponent_isClosed rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
      chemicalFieldPositive chemicalFieldConvergence eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
      coarse word).preimage homeomorph.continuous
  apply continuous_zero_outside_closed_cell_of_dense born dense (homeomorph ⁻¹' cell) closed extension
  rintro ⟨depth, vertex⟩ outside
  change homeomorph (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) ∉ cell at outside
  change extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) = 0
  rw [globalBorn]
  by_cases large : coarse + 1 ≤ depth
  · obtain ⟨fine, equality⟩ := Nat.exists_eq_add_of_le large
    have depthIdentity : depth = coarse + fine + 1 := by omega
    clear equality
    subst depth
    rw [actualBlockZeroTowerStage_tail]
    by_contra nonzero
    obtain ⟨localVertex, birthIdentity, valueNonzero⟩ := actualBlockZeroExtension_nonzero_birth rule coarse fine
      (generationWordEdge rule coarse (fun index => (word index).1))
      (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential fine)
      vertex.val nonzero
    have retained : ((rule.generation fine).network.openGraph
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)).Reachable
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) localVertex := by
      by_contra absent
      simp only [actualElectricalComponentStagePotential, rootedElectricalStagePotential, dif_neg absent] at valueNonzero
      exact valueNonzero rfl
    apply outside
    rw [birth]
    dsimp only [cell]
    unfold actualChemicalWordComponent
    rw [dif_pos live]
    refine ⟨actualChemicalCellVertex rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
      coarse (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      fine (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live fine ⟨localVertex, retained⟩), ?_⟩
    rw [actualChemicalCellInclusion_born]
    unfold actualComponentFiniteInclusion
    have verticesEqual : retainedBlockComponentEmbedding rule (stationaryConfiguration rule marks.val) chemicalCoherent coarse fine
        (generationWordEdge rule coarse (fun index => (word index).1)) (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
        (actual_word_component_anchor_retained rule marks.val marks.property.2.1 coarse word live)
        (actualElectricalComponentBlockVertex rule p positive belowOne fixedPoint growth value marks coarse word live fine ⟨localVertex, retained⟩) = vertex := by
      apply Subtype.ext
      exact birthIdentity
    let data := actual_block_lengths_of_terminal_field rule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalFieldPositive chemicalFieldConvergence
    exact congrArg (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val) chemicalCoherent chemicalGrowth
      chemicalGrowthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint chemicalGrowth amplitude chemicalValue marks.val)
      data.1 data.2.1 data.2.2 (coarse + fine + 1)) verticesEqual
  · simp only [actualBlockZeroTowerStage, dif_neg large]

end
end IGSIII34.ResistanceLimit

