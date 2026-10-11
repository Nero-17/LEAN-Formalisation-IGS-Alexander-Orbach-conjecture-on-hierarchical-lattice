import IGSIII.Mass.CylinderBoundaryLaw
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Deterministic small-mass control for finite probability partitions.
This is the measure-theoretic lower-mass step; actual frontier bounds and
cylinder atoms are assembled separately, and are not assumed by the final
actual-model spectral theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

theorem small_positive_partition_mass_le
    {Point Index : Type*} [MeasurableSpace Point] [Fintype Index]
    (measure : Measure Point) (index : Point → Index) (weight : Index → ℝ)
    (atoms : ∀ label, measure {point | index point = label} = ENNReal.ofReal (weight label))
    (threshold : ℝ) :
    measure {point | 0 < weight (index point) ∧ weight (index point) ≤ threshold} ≤
      ((Finset.univ.filter (fun label => 0 < weight label)).card : ℝ≥0∞) *
        ENNReal.ofReal threshold := by
  classical
  have subset : {point | 0 < weight (index point) ∧ weight (index point) ≤ threshold} ⊆
      ⋃ label : Index, {point | index point = label ∧ 0 < weight label ∧ weight label ≤ threshold} := by
    intro point property
    exact Set.mem_iUnion.mpr ⟨index point, rfl, property⟩
  have atomBound (label : Index) :
      measure {point | index point = label ∧ 0 < weight label ∧ weight label ≤ threshold} ≤
        if 0 < weight label then ENNReal.ofReal threshold else 0 := by
    by_cases positive : 0 < weight label
    · rw [if_pos positive]
      by_cases small : weight label ≤ threshold
      · have inclusion : {point | index point = label ∧ 0 < weight label ∧ weight label ≤ threshold} ⊆
            {point | index point = label} := fun _ property => property.1
        exact ((measure_mono inclusion).trans_eq (atoms label)).trans
          (ENNReal.ofReal_le_ofReal small)
      · simp only [small, and_false, Set.setOf_false, measure_empty]
        exact bot_le
    · simp [positive]
  calc
    _ ≤ measure (⋃ label : Index,
        {point | index point = label ∧ 0 < weight label ∧ weight label ≤ threshold}) := measure_mono subset
    _ ≤ ∑ label : Index, measure
        {point | index point = label ∧ 0 < weight label ∧ weight label ≤ threshold} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ label : Index, if 0 < weight label then ENNReal.ofReal threshold else 0 :=
      Finset.sum_le_sum (fun label _ => atomBound label)
    _ = _ := by
      rw [← Finset.sum_filter]
      simp

theorem ae_partition_mass_eventually_lower
    {Point : Type*} [MeasurableSpace Point]
    (measure : Measure Point) (Index : ℕ → Type*) [∀ depth, Fintype (Index depth)]
    (index : ∀ depth, Point → Index depth) (weight : ∀ depth, Index depth → ℝ)
    (atoms : ∀ depth label,
      measure {point | index depth point = label} = ENNReal.ofReal (weight depth label))
    (threshold : ℕ → ℝ)
    (summable : (∑' depth,
      ((Finset.univ.filter (fun label : Index depth => 0 < weight depth label)).card : ℝ≥0∞) *
        ENNReal.ofReal (threshold depth)) ≠ ∞) :
    ∀ᵐ point ∂measure, ∀ᶠ depth in atTop,
      0 < weight depth (index depth point) → threshold depth < weight depth (index depth point) := by
  classical
  have finiteSum : (∑' depth, measure {point |
      0 < weight depth (index depth point) ∧ weight depth (index depth point) ≤ threshold depth}) ≠ ∞ :=
    ne_top_of_le_ne_top summable (ENNReal.tsum_le_tsum (fun depth =>
      small_positive_partition_mass_le measure (index depth) (weight depth) (atoms depth) (threshold depth)))
  have result := ae_eventually_notMem finiteSum
  filter_upwards [result] with point bounded
  filter_upwards [bounded] with depth property
  intro positive
  exact lt_of_not_ge (fun small => property ⟨positive, small⟩)

end
end IGSIII34.Spectral
