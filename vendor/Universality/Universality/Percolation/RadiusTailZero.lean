import Universality.Percolation.RadiusSupport
import Mathlib.Analysis.Normed.Group.Tannery

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter FiniteNetwork
open scoped Topology
attribute [local irreducible] expectedRadiusBirth expectedClusterBirthPower

theorem Classical.limitingRootRadiusTailProbability_tendsto_zero {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Tendsto (rule.limitingRootRadiusTailProbability p) atTop (𝓝 0) := by
  obtain ⟨bound, hbound, hsupport⟩ := h.radius_birth_support
  have hmass := (rule.birth_mass_hasSum h.edges_gt_one h.vertices_gt_two hp hp').summable
  have hidentity (n : ℕ) : (∑' size : ℕ, (size : ℝ) * rule.expectedClusterBirth p size n) =
      rule.expectedClusterBirthPower p 1 n := by
    simpa only [pow_one] using (rule.expectedClusterBirthPower_hasSum p 1 n).tsum_eq
  simp_rw [hidentity] at hmass
  have hlimit : Tendsto
      (fun radius : ℕ => ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedRadiusBirth p radius n)
      atTop (𝓝 (∑' _n : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence hmass
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop
        (bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)] with radius hradius
      rw [hsupport n p radius hradius, mul_zero]
    · apply Filter.Eventually.of_forall
      intro radius n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (rule.expectedRadiusBirth_bounds hp hp' radius n).1)]
      exact mul_le_mul_of_nonneg_left (rule.expectedRadiusBirth_bounds hp hp' radius n).2 (by positivity)
  have hscaled := hlimit.const_mul (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2))
  change Tendsto (fun radius : ℕ => (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)) *
    ∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 1) * rule.expectedRadiusBirth p radius n) atTop (𝓝 0)
  simpa only [tsum_zero, mul_zero] using hscaled

end
end Universality.Rule
