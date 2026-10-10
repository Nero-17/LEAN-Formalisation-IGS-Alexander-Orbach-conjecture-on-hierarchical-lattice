import IGSIII.Geometry.ProjectionTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

theorem levyProkhorovEDist_map_le_of_lipschitz_one
    {Source Target : Type*} [MetricSpace Source] [MeasurableSpace Source] [BorelSpace Source]
    [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    (first second : Measure Source) (map : Source → Target) (lipschitz : LipschitzWith 1 map) :
    levyProkhorovEDist (first.map map) (second.map map) ≤ levyProkhorovEDist first second := by
  have measurable := lipschitz.continuous.measurable
  have thickening_inclusion (radius : ℝ) (event : Set Target) :
      Metric.thickening radius (map ⁻¹' event) ⊆ map ⁻¹' Metric.thickening radius event := by
    intro point belongs
    obtain ⟨nearby, nearby_belongs, close⟩ := Metric.mem_thickening_iff.mp belongs
    apply Metric.mem_thickening_iff.mpr
    refine ⟨map nearby, nearby_belongs, ?_⟩
    have contraction : dist (map point) (map nearby) ≤ dist point nearby := by
      simpa only [NNReal.coe_one, one_mul] using lipschitz.dist_le_mul point nearby
    exact contraction.trans_lt close
  apply levyProkhorovEDist_le_of_forall
  intro epsilon event epsilon_large epsilon_finite event_measurable
  rw [Measure.map_apply measurable event_measurable,
    Measure.map_apply measurable event_measurable,
    Measure.map_apply measurable Metric.isOpen_thickening.measurableSet,
    Measure.map_apply measurable Metric.isOpen_thickening.measurableSet]
  exact ⟨(left_measure_le_of_levyProkhorovEDist_lt epsilon_large (measurable event_measurable)).trans
      (add_le_add (measure_mono (thickening_inclusion _ _)) le_rfl),
    (right_measure_le_of_levyProkhorovEDist_lt epsilon_large (measurable event_measurable)).trans
      (add_le_add (measure_mono (thickening_inclusion _ _)) le_rfl)⟩

/-- Moving all but a small exceptional mass by at most a fixed radius gives
the stated genuine Prokhorov bound. -/
theorem levyProkhorovEDist_map_le_of_exceptional_set
    {Sample Space : Type*} [MeasurableSpace Sample] [MetricSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (measure : Measure Sample) (first second : Sample → Space)
    (first_measurable : Measurable first) (second_measurable : Measurable second)
    (bad : Set Sample) (radius : ℝ) (radius_nonnegative : 0 ≤ radius)
    (close : ∀ᵐ sample ∂measure, sample ∉ bad → dist (first sample) (second sample) ≤ radius) :
    levyProkhorovEDist (measure.map first) (measure.map second) ≤ ENNReal.ofReal radius + measure bad := by
  apply levyProkhorovEDist_le_of_forall
  intro epsilon event epsilon_large epsilon_finite event_measurable
  have radius_large : radius < epsilon.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal radius_nonnegative epsilon_finite.ne).mp
      ((le_add_right le_rfl).trans_lt epsilon_large)
  have bad_small : measure bad ≤ epsilon :=
    (le_add_left le_rfl).trans epsilon_large.le
  have transport (first_map second_map : Sample → Space)
      (first_map_measurable : Measurable first_map) (second_map_measurable : Measurable second_map)
      (near : ∀ᵐ sample ∂measure, sample ∉ bad → dist (first_map sample) (second_map sample) ≤ radius) :
      measure.map first_map event ≤ measure.map second_map (Metric.thickening epsilon.toReal event) + epsilon := by
    rw [Measure.map_apply first_map_measurable event_measurable,
      Measure.map_apply second_map_measurable Metric.isOpen_thickening.measurableSet]
    have included : measure (first_map ⁻¹' event) ≤
        measure ((second_map ⁻¹' Metric.thickening epsilon.toReal event) ∪ bad) := by
      apply measure_mono_ae
      filter_upwards [near] with sample near
      intro belongs
      by_cases exceptional : sample ∈ bad
      · exact Or.inr exceptional
      · exact Or.inl (Metric.mem_thickening_iff.mpr ⟨first_map sample, belongs,
          by simpa only [dist_comm] using (near exceptional).trans_lt radius_large⟩)
    exact included.trans ((measure_union_le _ _).trans (add_le_add le_rfl bad_small))
  exact ⟨transport first second first_measurable second_measurable close,
    transport second first second_measurable first_measurable (by simpa only [dist_comm] using close)⟩

end
end IGSIII.Geometry
