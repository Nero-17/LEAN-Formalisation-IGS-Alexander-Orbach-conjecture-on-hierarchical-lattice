import Universality.Probability.L2Characteristic

namespace Universality
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem real_eq_of_characteristic_phases (x y : ℝ)
    (h : ∀ t : ℝ, Complex.exp ((t * x : ℝ) * Complex.I) =
      Complex.exp ((t * y : ℝ) * Complex.I)) : x = y := by
  apply dirac_eq_dirac_iff.mp
  apply Measure.ext_of_charFun
  funext t
  simpa only [charFun_apply_real, integral_dirac, Complex.ofReal_mul] using h t

/-- A positive-weight term in a convex average in the complex unit disk must
be one whenever the average is one. -/
theorem weighted_characteristic_eq_one {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (values : ι → ℂ)
    (hweight : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hvalues : ∀ i, ‖values i‖ ≤ 1)
    (hsum : ∑ i, (weight i : ℂ) * values i = 1)
    (i : ι) (hpositive : 0 < weight i) : values i = 1 := by
  have hreal : ∑ j, weight j * (values j).re = ∑ j, weight j := by
    have h := congrArg Complex.re hsum
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.one_re, hmass] using h
  have hterm : weight i * (values i).re = weight i :=
    (Finset.sum_eq_sum_iff_of_le (fun j _ =>
      mul_le_of_le_one_right (hweight j) ((Complex.re_le_norm _).trans (hvalues j)))).mp
      hreal i (Finset.mem_univ _)
  have hre : (values i).re = 1 := mul_left_cancel₀ hpositive.ne' (by simpa only [mul_one] using hterm)
  apply Complex.ext
  · simpa using hre
  · have hle : ‖values i‖ ≤ (values i).re := by rw [hre]; exact hvalues i
    simpa using (RCLike.im_eq_zero_of_le hle)

/-- The analogous rigidity statement at any point of the unit circle. -/
theorem weighted_characteristic_eq_unit {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (values : ι → ℂ) (unit : ℂ)
    (hweight : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hvalues : ∀ i, ‖values i‖ ≤ 1) (hunit : ‖unit‖ = 1)
    (hsum : ∑ i, (weight i : ℂ) * values i = unit)
    (i : ι) (hpositive : 0 < weight i) : values i = unit := by
  have hne : unit ≠ 0 := by intro hz; simpa [hz] using hunit
  have hratio := weighted_characteristic_eq_one weight (fun j => values j / unit)
    hweight hmass (fun j => by simpa [norm_div, hunit] using hvalues j)
    (by simp only [← mul_div_assoc, ← Finset.sum_div, hsum, div_self hne]) i hpositive
  exact (div_eq_one_iff_eq hne).mp hratio

end
end Universality

