import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.Defs

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem positive_differentiable_local_exponential_comparison (function : ℝ → ℝ) (center : ℝ)
    (hdifferentiable : DifferentiableAt ℝ function center) (hpositive : 0 < function center) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ᶠ point in 𝓝 center, 0 < function point ∧
      function point ≤ Real.exp (rate * |point - center|) * function center ∧
      function center ≤ Real.exp (rate * |point - center|) * function point := by
  obtain ⟨rate, hrate, hbound⟩ := ((hdifferentiable.log hpositive.ne').isBigO_sub).exists_pos
  refine ⟨rate, hrate, ?_⟩
  filter_upwards [hbound.bound, hdifferentiable.continuousAt.eventually (lt_mem_nhds hpositive)] with point hbound hpoint
  simp only [Real.norm_eq_abs] at hbound
  have habs := abs_le.mp hbound
  refine ⟨hpoint, ?_, ?_⟩
  · calc
      function point = Real.exp (Real.log (function point)) := (Real.exp_log hpoint).symm
      _ ≤ Real.exp (rate * |point - center| + Real.log (function center)) :=
        Real.exp_le_exp.mpr (by linarith [habs.2])
      _ = _ := by rw [Real.exp_add, Real.exp_log hpositive]
  · calc
      function center = Real.exp (Real.log (function center)) := (Real.exp_log hpositive).symm
      _ ≤ Real.exp (rate * |point - center| + Real.log (function point)) :=
        Real.exp_le_exp.mpr (by linarith [habs.1])
      _ = _ := by rw [Real.exp_add, Real.exp_log hpoint]

theorem finite_positive_differentiable_exponential_comparison {ι : Type*} [Fintype ι]
    (function : ι → ℝ → ℝ) (center : ℝ)
    (hdifferentiable : ∀ i, DifferentiableAt ℝ (function i) center)
    (hpositive : ∀ i, 0 < function i center) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ᶠ point in 𝓝 center, ∀ i, 0 < function i point ∧
      function i point ≤ Real.exp (rate * |point - center|) * function i center ∧
      function i center ≤ Real.exp (rate * |point - center|) * function i point := by
  classical
  choose rate hrate hcomparison using fun i =>
    positive_differentiable_local_exponential_comparison (function i) center (hdifferentiable i) (hpositive i)
  refine ⟨(∑ i, rate i) + 1, add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hrate i).le)) zero_lt_one, ?_⟩
  have hall : ∀ᶠ point in 𝓝 center, ∀ i, 0 < function i point ∧
      function i point ≤ Real.exp (rate i * |point - center|) * function i center ∧
      function i center ≤ Real.exp (rate i * |point - center|) * function i point :=
    Filter.eventually_all.mpr hcomparison
  filter_upwards [hall] with point hpoint
  intro i
  have hi : rate i ≤ (∑ j, rate j) + 1 := by
    have hs := Finset.single_le_sum (s := Finset.univ) (f := rate)
      (fun j _ => (hrate j).le) (Finset.mem_univ i)
    linarith
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi (abs_nonneg (point - center)))
  exact ⟨(hpoint i).1,
    (hpoint i).2.1.trans (mul_le_mul_of_nonneg_right he (hpositive i).le),
    (hpoint i).2.2.trans (mul_le_mul_of_nonneg_right he (hpoint i).1.le)⟩

end
end Universality


