import IGSIII34.Diffusion.ActualDiscreteClockRescaleCompletion20261011
import IGSIII34.Diffusion.ActualPaperDeterministicLawCompletion20261011
import IGSIII34.Diffusion.ActualPaperDeterministicRatioCompletion20261011
import IGSIII34.Diffusion.ActualWeightedClockRescaledCadlagLawCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
  (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance paperDiscreteDeterministicLawMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance paperDiscreteDeterministicLawBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

def actualPaperDiscreteDeterministicGlobalLawCompletion20261011 (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualDiscreteClockRescaledGlobalLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive
    (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive false)
    (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive false)
    depth initial

def actualPaperDiscreteDeterministicCadlagLawCompletion20261011 (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualDiscreteClockRescaledCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive
    (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive false)
    (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive false)
    depth initial

theorem actualPaperDiscreteDeterministicCadlagLaw_val_completion20261011 (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualPaperDiscreteDeterministicCadlagLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial).map measurable_subtype_coe.aemeasurable =
      actualPaperDiscreteDeterministicGlobalLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial := by
  exact actualDiscreteClockRescaledCadlagLaw_val_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive _ _ depth initial

end
end IGSIII34.Diffusion


