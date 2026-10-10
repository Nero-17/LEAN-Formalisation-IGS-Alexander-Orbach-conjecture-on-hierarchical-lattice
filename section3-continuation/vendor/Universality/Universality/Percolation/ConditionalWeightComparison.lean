import Universality.Analysis.LocalExponentialComparison
import Universality.Percolation.VertexMomentRecursion
import Universality.Percolation.ReliabilityDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Universality.FiniteNetwork
noncomputable section
open Filter
open scoped Topology
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem differentiableAt_bernoulliWeight (configuration : Configuration edges) (p : ℝ) :
    DifferentiableAt ℝ (fun q => bernoulliWeight q configuration) p := by
  unfold bernoulliWeight
  apply DifferentiableAt.fun_finsetProd
  intro edge _
  cases configuration edge <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- Uniform exponential comparison of every actual one-cell conditional
configuration weight, including its fixed zero pattern. -/
theorem conditionalCellWeight_local_exponential_comparison (critical : ℝ)
    (hc : 0 < critical) (hc' : critical < 1)
    (hpositive : 0 < R.reliability critical) (hless : R.reliability critical < 1) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ᶠ p in 𝓝 critical, ∀ opened configuration,
      R.conditionalCellWeight p opened configuration ≤
        Real.exp (rate * |p - critical|) * R.conditionalCellWeight critical opened configuration ∧
      R.conditionalCellWeight critical opened configuration ≤
        Real.exp (rate * |p - critical|) * R.conditionalCellWeight p opened configuration := by
  have hdifferentiable (index : Bool × Configuration edges) : DifferentiableAt ℝ
      (fun p => bernoulliWeight p index.2 / (if index.1 then R.reliability p else 1 - R.reliability p)) critical := by
    apply (differentiableAt_bernoulliWeight index.2 critical).div
    · cases index.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (differentiableAt_const (c := (1 : ℝ))).sub (R.hasDerivAt_reliability critical).differentiableAt
      · exact (R.hasDerivAt_reliability critical).differentiableAt
    · cases index.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (sub_pos.mpr hless).ne'
      · exact hpositive.ne'
  have hweightPositive (index : Bool × Configuration edges) :
      0 < bernoulliWeight critical index.2 /
        (if index.1 then R.reliability critical else 1 - R.reliability critical) := by
    apply div_pos (bernoulliWeight_pos hc hc' _)
    cases index.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_pos.mpr hless
    · exact hpositive
  obtain ⟨rate, hrate, hcomparison⟩ := finite_positive_differentiable_exponential_comparison
    (fun index : Bool × Configuration edges => fun p => bernoulliWeight p index.2 /
      (if index.1 then R.reliability p else 1 - R.reliability p)) critical hdifferentiable hweightPositive
  refine ⟨rate, hrate, ?_⟩
  filter_upwards [hcomparison] with p hp
  intro opened configuration
  by_cases hcross : R.crosses configuration = opened
  · simpa only [conditionalCellWeight, hcross, ↓reduceIte] using (hp (opened, configuration)).2
  · simp only [conditionalCellWeight, hcross, ↓reduceIte, zero_div, mul_zero, le_refl, and_self]

end
end Universality.FiniteNetwork


