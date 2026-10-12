import IGSIII34.Diffusion.ActualDiscreteCadlagWholeWeakCompletion
import IGSIII34.Diffusion.ActualContinuousCadlagWholeWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
local instance actualPaperSameLawElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance actualPaperSameLawElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

theorem actual_paper_discrete_cadlag_same_law
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalGlobalJ1LawCompletion
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive initial depth)
      atTop (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion
        (countableTimeContinuousSampleCompletion times dense)
        (countableTimeContinuousSample_continuous_completion times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion times dense)).aemeasurable))) :
    Tendsto (fun depth => actualPaperDiscreteElectricalCadlagLawCompletion
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive initial depth)
      atTop (𝓝 (continuousCadlagProbabilityCompletion limitLaw
        (countableTimeContinuousSampleCompletion times dense)
        (countableTimeContinuousSample_continuous_completion times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion times dense))) := by
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩) => SkorokhodCadlagCompletion path)
  simpa only [actualPaperDiscreteElectricalCadlagLaw_val_completion,
    continuousCadlagProbability_val_completion] using weak

theorem actual_paper_continuous_cadlag_same_law
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualPaperContinuousElectricalGlobalJ1LawCompletion
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive initial depth)
      atTop (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion
        (countableTimeContinuousSampleCompletion times dense)
        (countableTimeContinuousSample_continuous_completion times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion times dense)).aemeasurable))) :
    Tendsto (fun depth => actualPaperContinuousElectricalCadlagLawCompletion
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive initial depth)
      atTop (𝓝 (continuousCadlagProbabilityCompletion limitLaw
        (countableTimeContinuousSampleCompletion times dense)
        (countableTimeContinuousSample_continuous_completion times dense)
        (countableTimeContinuousSample_evaluation_measurable_completion times dense))) := by
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩) => SkorokhodCadlagCompletion path)
  simpa only [actualPaperContinuousElectricalCadlagLaw_val_completion,
    continuousCadlagProbability_val_completion] using weak

end
end IGSIII34.ResistanceLimit
