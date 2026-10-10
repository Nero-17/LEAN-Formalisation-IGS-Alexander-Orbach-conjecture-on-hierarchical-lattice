import Universality.Examples.TieGemCriticalBounds
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Differentiate the actual reliability polynomial. -/
theorem gem_reliability_deriv (p : ℝ) :
    deriv gemRule.network.reliability p = 2 * p + 4 * p ^ 3 - 6 * p ^ 5 := by
  have hfun : gemRule.network.reliability =
      triangleNetwork.reliability ∘ twoEdgePathNetwork.reliability :=
    funext (Rule.mul_reliability triangleRule twoEdgePathRule)
  have hh := (triangleNetwork.hasDerivAt_reliability (twoEdgePathNetwork.reliability p)).comp p
    (twoEdgePathNetwork.hasDerivAt_reliability p)
  rw [hfun, hh.deriv, triangle_reliabilityPolynomial, twoEdgePath_reliabilityPolynomial,
    twoEdgePath_reliability]
  norm_num [Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_X_pow]
  ring

/-- The rigorous interval certifies the four-place value 1.6239. -/
theorem gem_critical_response_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (162385 : ℝ) / 100000 < deriv gemRule.network.reliability p ∧
      deriv gemRule.network.reliability p < (162395 : ℝ) / 100000 := by
  obtain ⟨hlower, hupper⟩ := gem_critical_point_rational_bounds p hp hp' hfixed
  have hl3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8191725 / 10000000) hlower.le 3
  have hl5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8191725 / 10000000) hlower.le 5
  have hu3 := pow_le_pow_left₀ hp.le hupper.le 3
  have hu5 := pow_le_pow_left₀ hp.le hupper.le 5
  norm_num at hl3 hl5 hu3 hu5
  rw [gem_reliability_deriv]
  constructor <;> linarith

/-- Both actual cyclic models share this certified response interval. -/
theorem tie_critical_response_bounds_of_gem (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (162385 : ℝ) / 100000 < deriv tieRule.network.reliability (p ^ 2) ∧
      deriv tieRule.network.reliability (p ^ 2) < (162395 : ℝ) / 100000 := by
  rw [← tie_gem_response p hfixed]
  exact gem_critical_response_rational_bounds p hp hp' hfixed

end
end Universality
