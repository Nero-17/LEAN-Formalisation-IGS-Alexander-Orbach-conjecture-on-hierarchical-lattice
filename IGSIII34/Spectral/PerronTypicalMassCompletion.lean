import IGSIII34.Spectral.TypicalCylinderMassCompletion
import Mathlib.Analysis.SpecificLimits.Basic

/-! A Perron frontier bound gives the typical lower mass estimate without
inverse branching-mass moments. Actual component counts are instantiated
separately, and no independence assumption is used here. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

theorem partition_Perron_threshold_summable
    (Index : ℕ → Type*) [∀ depth, Fintype (Index depth)]
    (weight : ∀ depth, Index depth → ℝ)
    (radius coefficient : ℝ) (radiusPositive : 0 < radius)
    (coefficientNonnegative : 0 ≤ coefficient)
    (countBound : ∀ depth,
      ((Finset.univ.filter (fun label : Index depth => 0 < weight depth label)).card : ℝ) ≤
        coefficient * radius ^ depth)
    (ratio : ℝ) (ratioNonnegative : 0 ≤ ratio) (ratioBelowOne : ratio < 1) :
    (∑' depth,
      ((Finset.univ.filter (fun label : Index depth => 0 < weight depth label)).card : ℝ≥0∞) *
        ENNReal.ofReal ((radius ^ depth)⁻¹ * ratio ^ depth)) ≠ ∞ := by
  classical
  have bounded (depth : ℕ) :
      ((Finset.univ.filter (fun label : Index depth => 0 < weight depth label)).card : ℝ≥0∞) *
        ENNReal.ofReal ((radius ^ depth)⁻¹ * ratio ^ depth) ≤
          ENNReal.ofReal coefficient * (ENNReal.ofReal ratio) ^ depth := by
    have nonnegative : 0 ≤ (radius ^ depth)⁻¹ * ratio ^ depth := by positivity
    have realBound := mul_le_mul_of_nonneg_right (countBound depth) nonnegative
    have cancelled : coefficient * radius ^ depth * ((radius ^ depth)⁻¹ * ratio ^ depth) =
        coefficient * ratio ^ depth := by
      field_simp
    rw [cancelled] at realBound
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [← ENNReal.ofReal_pow ratioNonnegative, ← ENNReal.ofReal_mul coefficientNonnegative]
    exact ENNReal.ofReal_le_ofReal realBound
  have geometric : (∑' depth : ℕ, (ENNReal.ofReal ratio) ^ depth) ≠ ∞ :=
    (tsum_geometric_lt_top.mpr (by simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr ratioBelowOne)).ne
  have finite : (∑' depth : ℕ, ENNReal.ofReal coefficient * (ENNReal.ofReal ratio) ^ depth) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top geometric
  exact ne_top_of_le_ne_top finite (ENNReal.tsum_le_tsum bounded)

theorem ae_partition_Perron_mass_eventually_lower
    {Point : Type*} [MeasurableSpace Point]
    (measure : Measure Point) (Index : ℕ → Type*) [∀ depth, Fintype (Index depth)]
    (index : ∀ depth, Point → Index depth) (weight : ∀ depth, Index depth → ℝ)
    (atoms : ∀ depth label,
      measure {point | index depth point = label} = ENNReal.ofReal (weight depth label))
    (radius coefficient : ℝ) (radiusPositive : 0 < radius)
    (coefficientNonnegative : 0 ≤ coefficient)
    (countBound : ∀ depth,
      ((Finset.univ.filter (fun label : Index depth => 0 < weight depth label)).card : ℝ) ≤
        coefficient * radius ^ depth)
    (ratio : ℝ) (ratioNonnegative : 0 ≤ ratio) (ratioBelowOne : ratio < 1) :
    ∀ᵐ point ∂measure, ∀ᶠ depth in atTop,
      0 < weight depth (index depth point) →
        ratio ^ depth < weight depth (index depth point) * radius ^ depth := by
  have lower := ae_partition_mass_eventually_lower measure Index index weight atoms
    (fun depth => (radius ^ depth)⁻¹ * ratio ^ depth)
    (partition_Perron_threshold_summable Index weight radius coefficient radiusPositive
      coefficientNonnegative countBound ratio ratioNonnegative ratioBelowOne)
  filter_upwards [lower] with point property
  filter_upwards [property] with depth property
  intro positive
  have inequality := property positive
  have multiplied := mul_lt_mul_of_pos_right inequality (pow_pos radiusPositive depth)
  have cancelled : (radius ^ depth)⁻¹ * ratio ^ depth * radius ^ depth = ratio ^ depth := by
    field_simp
  rwa [cancelled] at multiplied

end
end IGSIII34.Spectral
