import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Prokhorov control under a bounded projection

The same underlying measure is pushed forward by two nearby maps. The proof
uses measurable thickenings directly and does not assume a coupling theorem.
This supplies the projection-error estimate in the chemical GHP construction.
-/

set_option autoImplicit false

namespace IGSIII.Geometry

open MeasureTheory Metric Set
open Filter
open scoped ENNReal Topology

variable {Sample Space : Type*} [MeasurableSpace Sample] [MetricSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem map_measure_le_thickening_of_ae_dist_lt
    (measure : Measure Sample) {first second : Sample → Space}
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    {radius : ℝ} (close : ∀ᵐ sample ∂measure, dist (first sample) (second sample) < radius)
    {event : Set Space} (eventMeasurable : MeasurableSet event) :
    measure.map first event ≤ measure.map second (Metric.thickening radius event) := by
  rw [Measure.map_apply firstMeasurable eventMeasurable,
    Measure.map_apply secondMeasurable Metric.isOpen_thickening.measurableSet]
  apply measure_mono_ae
  filter_upwards [close] with sample sampleClose
  intro membership
  exact Metric.mem_thickening_iff.mpr ⟨first sample, membership,
    by simpa only [dist_comm] using sampleClose⟩

theorem levyProkhorovEDist_map_le_of_ae_dist_le
    (measure : Measure Sample) {first second : Sample → Space}
    (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (close : ∀ᵐ sample ∂measure, dist (first sample) (second sample) ≤ radius) :
    levyProkhorovEDist (measure.map first) (measure.map second) ≤ ENNReal.ofReal radius := by
  apply levyProkhorovEDist_le_of_forall
  intro epsilon event radiusLess epsilonFinite eventMeasurable
  have radiusLessReal : radius < epsilon.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal radiusNonnegative epsilonFinite.ne).mp radiusLess
  have closeStrict : ∀ᵐ sample ∂measure,
      dist (first sample) (second sample) < epsilon.toReal :=
    close.mono fun _ comparison => comparison.trans_lt radiusLessReal
  have reverseStrict : ∀ᵐ sample ∂measure,
      dist (second sample) (first sample) < epsilon.toReal := by
    simpa only [dist_comm] using closeStrict
  exact ⟨(map_measure_le_thickening_of_ae_dist_lt measure firstMeasurable secondMeasurable
      closeStrict eventMeasurable).trans (le_add_right le_rfl),
    (map_measure_le_thickening_of_ae_dist_lt measure secondMeasurable firstMeasurable
      reverseStrict eventMeasurable).trans (le_add_right le_rfl)⟩

theorem levyProkhorovEDist_projection_tendsto_zero
    (measure : Measure Sample) (projection : ℕ → Sample → Space) (inclusion : Sample → Space)
    (projectionMeasurable : ∀ depth, Measurable (projection depth))
    (inclusionMeasurable : Measurable inclusion) (mesh : ℕ → ℝ)
    (meshNonnegative : ∀ depth, 0 ≤ mesh depth)
    (vanishing : Tendsto mesh atTop (𝓝 0))
    (close : ∀ depth, ∀ᵐ sample ∂measure,
      dist (projection depth sample) (inclusion sample) ≤ mesh depth) :
    Tendsto (fun depth => levyProkhorovEDist (measure.map (projection depth))
      (measure.map inclusion)) atTop (𝓝 0) := by
  have upperConverges : Tendsto (fun depth => ENNReal.ofReal (mesh depth)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp vanishing
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upperConverges
    (fun _ => bot_le) (fun depth => levyProkhorovEDist_map_le_of_ae_dist_le measure
      (projectionMeasurable depth) inclusionMeasurable (meshNonnegative depth) (close depth))

end IGSIII.Geometry
