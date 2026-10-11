import IGSIII34.ResistanceLimit.ActualElectricalZeroSupport
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

variable (potential : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ)
  (boundaryZero : ∀ side : Bool, potential (rootedElectricalSkeletonPoint rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) 0
    (plantedVertex (rule.generation 0).network side)) = 0)


include birth live boundaryZero in
/-- Genuine completion-domain zero extension, with exact local energy and
restriction, and zero at every point outside the canonical closed cell. -/
theorem actualElectricalComponent_completed_zero_extension_in_chemical_cell
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (finite : actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) potential)
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks.val depth descendant state : ℝ) /
        chemicalGrowth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
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
      (∀ point, homeomorph point ∉ actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
        chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
        chemicalFieldPositive chemicalFieldConvergence coarse word → extension point = 0) ∧
      (∀ depth (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)),
        extension (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive rootMarks depth vertex) =
          actualBlockZeroTowerStage rule coarse (generationWordEdge rule coarse (fun index => (word index).1))
            (actualElectricalComponentStagePotential rule p positive belowOne fixedPoint growth value growthPositive marks coarse word potential) depth vertex.val) := by
  dsimp only
  obtain ⟨extension, domain, energy, restriction, globalBorn⟩ :=
    actualElectricalComponent_completed_zero_extension rule p positive belowOne fixedPoint growth value growthPositive
      marks coarse word live potential boundaryZero stationary finite
  refine ⟨extension, domain, energy, restriction, ?_, globalBorn⟩
  exact actualElectricalComponent_zero_outside_chemical_cell rule classicalRule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalGrowth amplitude chemicalGrowthPositive amplitudePositive chemicalValue chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
    homeomorph birth coarse word live eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    potential extension globalBorn

end
end IGSIII34.ResistanceLimit

