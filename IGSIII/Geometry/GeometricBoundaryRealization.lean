import IGSIII.Geometry.ProjectionTransport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- A measurable boundary map is constructed from the actual convergent
representative points. Its pushforward is approximated in Prokhorov distance. -/
theorem exists_measurable_geometric_boundary_limit
    {Sample Space : Type*} [MeasurableSpace Sample] [MetricSpace Space]
    [CompleteSpace Space] [Nonempty Space] [MeasurableSpace Space] [BorelSpace Space]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (representative : ℕ → Sample → Space)
    (measurable : ∀ depth, Measurable (representative depth))
    (ratio constant : ℝ) (ratio_nonnegative : 0 ≤ ratio) (ratio_lt_one : ratio < 1)
    (constant_nonnegative : 0 ≤ constant) (start : ℕ)
    (increments : ∀ᵐ sample ∂measure, ∀ depth,
      dist (representative (depth + start) sample) (representative (depth + start + 1) sample) ≤
        constant * ratio ^ depth) :
    ∃ boundary : Sample → Space,
      Measurable boundary ∧ IsProbabilityMeasure (measure.map boundary) ∧
      (∀ᵐ sample ∂measure, Tendsto (fun depth => representative depth sample) atTop (𝓝 (boundary sample))) ∧
      (∀ depth, ∀ᵐ sample ∂measure,
        dist (representative (depth + start) sample) (boundary sample) ≤ constant * ratio ^ depth / (1 - ratio)) ∧
      Tendsto (fun depth => levyProkhorovEDist (measure.map (representative depth))
        (measure.map boundary)) atTop (𝓝 0) := by
  let candidate : Sample → Space := fun sample =>
    limUnder atTop (fun depth => representative (depth + start) sample)
  have candidate_convergence : ∀ᵐ sample ∂measure,
      Tendsto (fun depth => representative (depth + start) sample) atTop (𝓝 (candidate sample)) := by
    filter_upwards [increments] with sample increment
    exact (cauchySeq_of_le_geometric ratio constant ratio_lt_one (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using increment)).tendsto_limUnder
  have candidate_measurable : AEMeasurable candidate measure :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun depth => (measurable (depth + start)).aemeasurable) candidate_convergence
  refine ⟨candidate_measurable.mk candidate, candidate_measurable.measurable_mk,
    Measure.isProbabilityMeasure_map candidate_measurable.measurable_mk.aemeasurable, ?_, ?_, ?_⟩
  · filter_upwards [candidate_convergence, candidate_measurable.ae_eq_mk] with sample convergence equality
    exact (tendsto_add_atTop_iff_nat start).mp (by simpa only [equality] using convergence)
  · intro depth
    filter_upwards [increments, candidate_convergence, candidate_measurable.ae_eq_mk]
      with sample increment convergence equality
    rw [← equality]
    exact dist_le_of_le_geometric_of_tendsto ratio constant ratio_lt_one (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using increment) convergence depth
  · apply (tendsto_add_atTop_iff_nat start).mp
    apply levyProkhorovEDist_projection_tendsto_zero measure
      (fun depth => representative (depth + start)) (candidate_measurable.mk candidate)
      (fun depth => measurable (depth + start)) candidate_measurable.measurable_mk
      (fun depth => constant * ratio ^ depth / (1 - ratio))
    · intro depth
      exact div_nonneg (mul_nonneg constant_nonnegative (pow_nonneg ratio_nonnegative depth))
        (sub_pos.mpr ratio_lt_one).le
    · simpa only [mul_zero, zero_div] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_nonnegative ratio_lt_one)).div_const (1 - ratio)
    · intro depth
      filter_upwards [increments, candidate_convergence, candidate_measurable.ae_eq_mk]
        with sample increment convergence equality
      rw [← equality]
      exact dist_le_of_le_geometric_of_tendsto ratio constant ratio_lt_one (by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using increment) convergence depth

end
end IGSIII.Geometry
