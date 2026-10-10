import IGSIII.Probability.LpRealOrder

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory
open scoped ENNReal

variable {Sample : Type*} [MeasurableSpace Sample] {measure : Measure Sample} {order : ℝ≥0∞}

theorem lp_le_inv_smul_of_smul_le {first second : Lp ℝ order measure}
    (scalar : ℝ) (positive : 0 < scalar) (comparison : scalar • first ≤ second) :
    first ≤ scalar⁻¹ • second := by
  have scaled := lp_smul_mono comparison scalar⁻¹ (inv_nonneg.mpr positive.le)
  simpa only [smul_smul, inv_mul_cancel₀ positive.ne', one_smul] using scaled

theorem lp_family_comparison_with_bounded_base
    (family : Set (Lp ℝ order measure)) (constant : ℝ) (constantPositive : 0 < constant)
    (comparison : ∀ first ∈ family, ∀ second ∈ family, first ≤ constant • second)
    (base : Lp ℝ order measure) (baseMember : base ∈ family)
    (value : Lp ℝ order measure) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (lowerBound : lower • base ≤ value) (upperBound : value ≤ upper • base) :
    ∀ member ∈ family,
      (upper * constant)⁻¹ • value ≤ member ∧ member ≤ (constant * lower⁻¹) • value := by
  intro member membership
  constructor
  · apply lp_inv_smul_le_of_le_smul (upper * constant) (mul_pos upperPositive constantPositive)
    have baseBelow := lp_smul_mono (comparison base baseMember member membership) upper upperPositive.le
    rw [smul_smul] at baseBelow
    exact upperBound.trans baseBelow
  · have scaled := lp_smul_mono (lp_le_inv_smul_of_smul_le lower lowerPositive lowerBound)
      constant constantPositive.le
    rw [smul_smul] at scaled
    exact (comparison member membership base baseMember).trans scaled

end IGSIII.Probability
