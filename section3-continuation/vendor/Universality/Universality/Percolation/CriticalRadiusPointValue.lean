import Universality.Percolation.CriticalRadiusPointExponent

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 500000
open Filter
open scoped Topology

theorem Classical.critical_radius_point_exponent_value {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (radiusExponent : ℝ)
    (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < rule.limitingRootRadiusProbability p radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (rule.limitingRootRadiusProbability p radius) /
      Real.log (radius : ℝ)) atTop (𝓝 (-1 - 1 / radiusExponent))) :
    radiusExponent = Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) /
      (Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) := by
  have hh := h.critical_radius_point_exponent_if_exists p hp hp' hfixed
    (-1 - 1 / radiusExponent) hpositive hlimit
  have hinverse : 1 / radiusExponent = (Real.log (rule.edges : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by linarith
  have hvalue := congrArg (fun x : ℝ => x⁻¹) hinverse
  simpa only [one_div, inv_inv, inv_div] using hvalue

end
end Universality.Rule
