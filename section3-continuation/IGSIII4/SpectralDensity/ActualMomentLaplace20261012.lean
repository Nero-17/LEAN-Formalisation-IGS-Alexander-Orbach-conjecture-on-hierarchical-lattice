import IGSIII34.Probability.FiniteTensorization
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability

/-- The Taylor bound used in Appendix C follows from the exponential tangent
inequality, with no bound on the support of the resistance law. -/
theorem exp_neg_le_quadratic20261012 (value : ℝ) (nonnegative : 0 ≤ value) :
    Real.exp (-value) ≤ 1 - value + value ^ 2 / 2 := by
  have derivative (point : ℝ) :
      HasDerivAt (fun argument : ℝ => 1 - argument + argument ^ 2 / 2 -
        Real.exp (-argument)) (-1 + point + Real.exp (-point)) point := by
    convert (((hasDerivAt_const point (1 : ℝ)).sub (hasDerivAt_id point)).add
      (((hasDerivAt_id point).pow 2).div_const 2)).sub
        ((Real.hasDerivAt_exp (-point)).comp point (hasDerivAt_id point).neg) using 1
    all_goals first | rfl | (ext argument; simp <;> ring) | (simp <;> ring)
  have monotonicity := monotone_of_hasDerivAt_nonneg derivative (by
    intro point
    change 0 ≤ -1 + point + Real.exp (-point)
    have tangent := Real.add_one_le_exp (-point)
    linarith)
  have comparison := monotonicity nonnegative
  simp only [neg_zero, Real.exp_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    sub_zero, add_zero, sub_self] at comparison
  linarith

/-- The uniform Laplace estimate starts from the actual first two moments.
It therefore applies at every finite recursive depth with variance at most eight. -/
theorem finiteMean_laplace_le20261012 {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (responseNonnegative : ∀ outcome, 0 ≤ response outcome)
    (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean weight (fun outcome => Real.exp (-response outcome / 18)) ≤ 23 / 24 := by
  have secondMoment : finiteMean weight (fun outcome => response outcome ^ 2) ≤ 9 := by
    rw [finiteVariance_eq_second_moment weight response normalized, meanOne] at varianceBound
    linarith
  have comparison : finiteMean weight (fun outcome => Real.exp (-response outcome / 18)) ≤
      finiteMean weight (fun outcome => 1 - response outcome / 18 +
        response outcome ^ 2 / 648) := by
    apply Finset.sum_le_sum
    intro outcome _
    apply mul_le_mul_of_nonneg_left _ (weightNonnegative outcome)
    have bound := exp_neg_le_quadratic20261012 (response outcome / 18)
      (div_nonneg (responseNonnegative outcome) (by norm_num))
    convert bound using 1 <;> first | rfl | ring
  have average : finiteMean weight (fun outcome => 1 - response outcome / 18 +
      response outcome ^ 2 / 648) = 1 - finiteMean weight response / 18 +
        finiteMean weight (fun outcome => response outcome ^ 2) / 648 := by
    simp only [finiteMean, mul_add, mul_sub, mul_one, ← mul_div_assoc,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, normalized]
  rw [average, meanOne] at comparison
  linarith

end
end IGSIII4.SpectralDensity
