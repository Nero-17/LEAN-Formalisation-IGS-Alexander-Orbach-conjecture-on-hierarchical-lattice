import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory

/-- Equality of ambient laws reflects equality of subtype laws even when
the subtype itself has not yet been shown to be a measurable ambient set. -/
theorem probability_subtype_val_map_injective
    {Ambient : Type*} [MeasurableSpace Ambient] (predicate : Ambient → Prop) :
    Function.Injective (fun law : ProbabilityMeasure {point : Ambient // predicate point} =>
      law.map measurable_subtype_coe.aemeasurable) := by
  intro first last same
  apply ProbabilityMeasure.toMeasure_injective
  ext subset measurableSubset
  obtain ⟨ambientSubset, ambientMeasurable, equality⟩ := MeasurableSpace.measurableSet_comap.mp measurableSubset
  have probabilities := congrArg (fun law : ProbabilityMeasure Ambient => (law : Measure Ambient) ambientSubset) same
  simpa only [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_subtype_coe ambientMeasurable, equality] using probabilities

end
end IGSIII34.Diffusion
