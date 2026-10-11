import IGSIII34.Diffusion.WholeCadlagIsometricTransport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter

/-- Whole-cadlag probability transport composes for arbitrary continuous
compact carrier maps; metric preservation is not required. -/
theorem skorokhodCadlagProbabilityMap_comp
    {First Middle Last : Type*}
    [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Middle] [CompactSpace Middle] [MeasurableSpace Middle] [BorelSpace Middle]
    [MetricSpace Last] [CompactSpace Last] [MeasurableSpace Last] [BorelSpace Last]
    (firstMapping : First → Middle) (firstContinuous : Continuous firstMapping)
    (lastMapping : Middle → Last) (lastContinuous : Continuous lastMapping)
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 First)) :
    (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
      firstMapping firstContinuous).measurable.aemeasurable).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        lastMapping lastContinuous).measurable.aemeasurable =
      law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (lastMapping ∘ firstMapping) (lastContinuous.comp firstContinuous)).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure _).map
    (skorokhodCadlagContinuousCarrierMapCompletion20261011 firstMapping firstContinuous)).map
    (skorokhodCadlagContinuousCarrierMapCompletion20261011 lastMapping lastContinuous) =
    (law : Measure _).map (skorokhodCadlagContinuousCarrierMapCompletion20261011
      (lastMapping ∘ firstMapping) (lastContinuous.comp firstContinuous))
  rw [Measure.map_map
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 lastMapping lastContinuous).measurable
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 firstMapping firstContinuous).measurable]
  apply Measure.map_congr
  exact Eventually.of_forall
    (skorokhodCadlagCarrierMap_comp firstMapping firstContinuous lastMapping lastContinuous)

end
end IGSIII34.Diffusion
