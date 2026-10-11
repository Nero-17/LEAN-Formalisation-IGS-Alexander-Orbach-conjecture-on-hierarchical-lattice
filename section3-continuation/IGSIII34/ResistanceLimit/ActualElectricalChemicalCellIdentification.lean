import IGSIII34.ResistanceLimit.ActualElectricalChemicalCellRange
import IGSIII34.Diffusion.ActualElectricalComponentInjectivity

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
/-- All intermediate range-closedness and injectivity inputs are discharged
by the actual stationary finite electrical inverse estimate. -/
theorem actualElectricalComponent_chemical_cell_identification
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks.val depth descendant state : ℝ) /
        chemicalGrowth ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
    Set.range (fun point => homeomorph (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live point)) =
    actualChemicalWordComponent rule classicalRule p positive belowOne fixedPoint chemicalGrowth amplitude
      chemicalGrowthPositive amplitudePositive chemicalValue marks.val marks.property.2.1 chemicalCoherent
      chemicalFieldPositive chemicalFieldConvergence coarse word ∧
    Function.Injective (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint
      growth value growthPositive marks (List.ofFn word) live) := by
  refine ⟨?_, ?_⟩
  · exact actualElectricalComponent_chemical_cell_range rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalGrowth amplitude chemicalGrowthPositive amplitudePositive chemicalValue chemicalCoherent chemicalFieldPositive chemicalFieldConvergence
      homeomorph birth coarse word live eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
      (actualElectricalComponentCompletionInclusion_closed_range rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary)
  · exact actualElectricalComponentCompletionInclusion_injective rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary

end
end IGSIII34.ResistanceLimit

