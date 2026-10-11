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

include classicalRule growthPositive in
theorem actualPaperDeterministicRatios_positive_of_classical_completion20261011
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale) (countingSpeed : Bool) :
    ∀ depth, 0 < actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed depth := by
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  exact actualPaperDeterministicClockRatio_positive_completion20261011 rule p growth growthPositive radiusPositive marks.val
    marks.property.1.1.2.1 chemicalScale chemicalScalePositive countingSpeed

local instance paperDeterministicLawMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance paperDeterministicLawBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

def actualPaperDeterministicGlobalLawCompletion20261011 (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualWeightedClockRescaledGlobalLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive countingSpeed
    (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed)
    (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed)
    depth initial

def actualPaperDeterministicCadlagLawCompletion20261011 (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :=
  actualWeightedClockRescaledCadlagLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive countingSpeed
    (actualPaperDeterministicClockRatioCompletion20261011 rule p growth marks.val chemicalScale chemicalScalePositive countingSpeed)
    (actualPaperDeterministicRatios_positive_of_classical_completion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed)
    depth initial

theorem actualPaperDeterministicCadlagLaw_val_completion20261011 (countingSpeed : Bool) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    (actualPaperDeterministicCadlagLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth initial).map measurable_subtype_coe.aemeasurable =
      actualPaperDeterministicGlobalLawCompletion20261011 rule classicalRule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed depth initial := by
  exact actualWeightedClockRescaledCadlagLaw_val_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed _ _ depth initial

end
end IGSIII34.Diffusion

