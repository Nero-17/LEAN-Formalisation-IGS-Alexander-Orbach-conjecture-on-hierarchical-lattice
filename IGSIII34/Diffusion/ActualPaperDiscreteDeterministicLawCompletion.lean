import IGSIII34.Diffusion.ActualDiscreteClockRescaleCompletion
import IGSIII34.Diffusion.ActualPaperDeterministicLawCompletion
import IGSIII34.Diffusion.ActualPaperDeterministicRatioCompletion
import IGSIII34.Diffusion.ActualWeightedClockRescaledCadlagLawCompletion

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

local instance paperDiscreteDeterministicLawMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance paperDiscreteDeterministicLawBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

def actualPaperDiscreteDeterministicGlobalLawCompletion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualDiscreteClockRescaledGlobalLawCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive
    (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive false)
    (actualPaperDeterministicRatios_positive_of_classical_completion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive false)
    depth initial

def actualPaperDiscreteDeterministicCadlagLawCompletion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualDiscreteClockRescaledCadlagLawCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive
    (actualPaperDeterministicClockRatioCompletion rule p growth marks.val chemicalScale chemicalScalePositive false)
    (actualPaperDeterministicRatios_positive_of_classical_completion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive false)
    depth initial

theorem actualPaperDiscreteDeterministicCadlagLaw_val_completion (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualPaperDiscreteDeterministicCadlagLawCompletion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial).map measurable_subtype_coe.aemeasurable =
      actualPaperDiscreteDeterministicGlobalLawCompletion rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive depth initial := by
  exact actualDiscreteClockRescaledCadlagLaw_val_completion rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive _ _ depth initial

end
end IGSIII34.Diffusion


