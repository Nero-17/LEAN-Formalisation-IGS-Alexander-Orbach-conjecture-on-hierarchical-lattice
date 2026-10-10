import Universality.Graph.UniformRootRadiusPointLaw
import Universality.Percolation.CriticalRadiusPointValue
import Universality.Examples.DiamondRadiusNonexistence

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem Classical.uniformRoot_critical_radius_power_bounds {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ radius : ℕ in atTop,
      lower * (radius : ℝ) ^ (-(Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) ≤
          rule.uniformRootRadiusTailProbability h.edges_gt_one p radius ∧
      rule.uniformRootRadiusTailProbability h.edges_gt_one p radius ≤
        upper * (radius : ℝ) ^ (-(Real.log (rule.edges : ℝ) -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  simp_rw [h.uniformRootRadiusTailProbability_eq_limiting p hp hp' hfixed]
  exact h.critical_radius_power_bounds p hp hp' hfixed

theorem Classical.uniformRoot_critical_radius_point_exponent_if_exists {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) (exponent : ℝ)
    (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < rule.uniformRootRadiusProbability h.edges_gt_one p radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (rule.uniformRootRadiusProbability h.edges_gt_one p radius) /
      Real.log (radius : ℝ)) atTop (𝓝 exponent)) :
    exponent = -1 - (Real.log (rule.edges : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  apply h.critical_radius_point_exponent_if_exists p hp hp' hfixed exponent
  · simpa only [h.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hpositive
  · simpa only [h.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hlimit

theorem Classical.uniformRoot_critical_radius_point_exponent_value {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) (radiusExponent : ℝ)
    (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < rule.uniformRootRadiusProbability h.edges_gt_one p radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (rule.uniformRootRadiusProbability h.edges_gt_one p radius) /
      Real.log (radius : ℝ)) atTop (𝓝 (-1 - 1 / radiusExponent))) :
    radiusExponent = Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) /
      (Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) := by
  apply h.critical_radius_point_exponent_value p hp hp' hfixed radiusExponent
  · simpa only [h.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hpositive
  · simpa only [h.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hlimit

end
end Universality.Rule

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem diamond_uniformRoot_radius_point_log_limit_nonexistent
    [Nonempty diamondRule.network.InteriorVertex] [NeZero diamondRule.edges]
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : diamondNetwork.reliability (p : ℝ) = p) :
    ¬ ∃ exponent : ℝ,
      (∀ᶠ radius : ℕ in atTop,
        0 < diamondRule.uniformRootRadiusProbability diamondRule_classical.edges_gt_one p radius) ∧
      Tendsto (fun radius : ℕ =>
        Real.log (diamondRule.uniformRootRadiusProbability diamondRule_classical.edges_gt_one p radius) /
          Real.log (radius : ℝ)) atTop (𝓝 exponent) := by
  intro ⟨exponent, hpositive, hlimit⟩
  apply diamond_radius_point_log_limit_nonexistent p hp hp' hfixed
  refine ⟨exponent, ?_, ?_⟩
  · simpa only [diamondRule_classical.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hpositive
  · simpa only [diamondRule_classical.uniformRootRadiusProbability_eq_limiting p hp hp' hfixed] using hlimit

end
end Universality
