import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory
open scoped ENNReal

variable {Sample : Type*} [MeasurableSpace Sample] {measure : Measure Sample} {order : ℝ≥0∞}

theorem lp_smul_mono {first second : Lp ℝ order measure} (comparison : first ≤ second)
    (scalar : ℝ) (nonnegative : 0 ≤ scalar) : scalar • first ≤ scalar • second := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [(Lp.coeFn_le first second).mpr comparison,
    Lp.coeFn_smul scalar first, Lp.coeFn_smul scalar second]
    with sample inequality firstEquality secondEquality
  simpa only [firstEquality, secondEquality, Pi.smul_apply, smul_eq_mul] using
    mul_le_mul_of_nonneg_left inequality nonnegative

theorem lp_inv_smul_le_of_le_smul {first second : Lp ℝ order measure}
    (scalar : ℝ) (positive : 0 < scalar) (comparison : first ≤ scalar • second) :
    scalar⁻¹ • first ≤ second := by
  have scaled := lp_smul_mono comparison scalar⁻¹ (inv_nonneg.mpr positive.le)
  simpa only [smul_smul, inv_mul_cancel₀ positive.ne', one_smul] using scaled

theorem lp_positive_of_positive_lower {first second : Lp ℝ order measure}
    (comparison : first ≤ second) (positive : ∀ᵐ sample ∂measure, 0 < first sample) :
    ∀ᵐ sample ∂measure, 0 < second sample := by
  filter_upwards [(Lp.coeFn_le first second).mpr comparison, positive] with sample inequality positivity
  exact positivity.trans_le inequality

end IGSIII.Probability
