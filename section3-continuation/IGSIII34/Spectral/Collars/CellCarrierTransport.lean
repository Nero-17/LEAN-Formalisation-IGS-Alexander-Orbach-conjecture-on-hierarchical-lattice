import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory

theorem homeomorph_pushforward_cell_mass
    {First Last : Type*} [TopologicalSpace First] [TopologicalSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (identification : First ≃ₜ Last) (measure : Measure First)
    (cell : Set First) (measurable : MeasurableSet cell) :
    (measure.map identification) (identification '' cell) = measure cell := by
  have imageMeasurable : MeasurableSet (identification '' cell) := by
    simpa only [identification.toMeasurableEquiv_coe] using
      identification.toMeasurableEquiv.measurableSet_image.mpr measurable
  rw [Measure.map_apply identification.measurable imageMeasurable]
  rw [Set.preimage_image_eq _ identification.injective]

/-- Singleton-null mass passes back through the actual carrier
homeomorphism; this applies before the closed chemical cell calculation. -/
theorem homeomorph_null_singletons_of_pushforward
    {First Last : Type*} [TopologicalSpace First] [TopologicalSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    [MeasurableSingletonClass First] [MeasurableSingletonClass Last]
    (identification : First ≃ₜ Last) (measure : Measure First)
    [NullSingletonClass (measure.map identification)] : NullSingletonClass measure := by
  constructor
  intro point
  have zero := measure_singleton (μ := measure.map identification) (identification point)
  rw [Measure.map_apply identification.measurable (measurableSet_singleton _)] at zero
  have preimage : identification ⁻¹' {identification point} = {point} := by
    ext other
    exact identification.injective.eq_iff
  rwa [preimage] at zero

end
end IGSIII34.Spectral
