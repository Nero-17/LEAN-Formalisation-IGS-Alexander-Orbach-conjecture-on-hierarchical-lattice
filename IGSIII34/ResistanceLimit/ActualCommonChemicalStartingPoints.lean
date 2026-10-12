import IGSIII34.ResistanceLimit.CommonChemicalDiracStarts
import IGSIII34.ResistanceLimit.ActualNaturalChemicalCarrier

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

local instance actualCommonStartingElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance actualCommonStartingElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩

/-- Every convergent actual finite starting-vertex sequence in the chosen
chemical common realization supplies the true electrical Dirac initial law. -/
theorem actual_common_chemical_dirac_starting_laws_tendsto
    {Ambient : Type*} [MetricSpace Ambient]
    (homeomorph : actualStationaryChemicalSpaceCompletion rule p positive belowOne fixedPoint growth value marks
      classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence ≃ₜ
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    (birthIdentity : ∀ depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth),
      homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ depth vertex) =
      actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)
    (target : actualStationaryChemicalSpaceCompletion rule p positive belowOne fixedPoint growth value marks
      classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient)
    (targetIsometry : Isometry target)
    (sources : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → Ambient)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)) < tolerance)
    (vertices : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (point : actualStationaryChemicalSpaceCompletion rule p positive belowOne fixedPoint growth value marks
      classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)
    (convergence : Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point))) :
    Tendsto (fun depth => (diracProba (vertices depth)).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val,marks.property.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 (diracProba (homeomorph point))) := by
  exact common_chemical_dirac_starting_laws_tendsto
    (Vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (Electrical := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩)
    homeomorph target targetIsometry
    (fun depth => actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth)
    (fun depth vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ depth vertex)
    (fun depth => measurable_of_finite _) birthIdentity sources placementClose vertices point convergence

end
end IGSIII34.ResistanceLimit
