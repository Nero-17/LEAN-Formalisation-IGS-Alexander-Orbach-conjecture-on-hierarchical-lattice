import Universality.Percolation.VertexInnovation
import Universality.Probability.GeometricL2Sum

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem Classical.vertex_innovation_sum_L2_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) :
    Tendsto (fun n : ℕ => eLpNorm (fun path =>
      (∑ k ∈ Finset.range n, ConfigurationHistory.vertexInnovation rule p state k (path (k + 1))) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨bound, hbound, hestimate⟩ := h.vertex_innovation_second_moment_bound p hp hp' hfixed
  apply geometric_second_moment_sum_tendsto_zero _ _ bound _ hbound.le
    ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  · exact fun n => hestimate n state
  · intro n
    exact ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected)
      (n + 1) (ConfigurationHistory.vertexInnovation rule p state n) 2

/-- The cumulative vertex reward differs from its predictable live-cell
response by a term that vanishes in L² at the mass-growth scale. -/
theorem Classical.vertex_reward_compensation_L2_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) :
    Tendsto (fun n : ℕ => eLpNorm (fun path =>
      (ConfigurationHistory.vertexMass rule state n path - ConfigurationHistory.vertexMass rule state 0 path -
        ∑ k ∈ Finset.range n, ConfigurationHistory.weightedPopulation rule state
          (rule.network.conditionalVertexMass p) k (path k)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  apply (h.vertex_innovation_sum_L2_zero p hp hp' hfixed state).congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  have hall := ae_all_iff.mpr (fun k =>
    ConfigurationHistory.vertexInnovation_eq_ae rule p hp hp' hfixed state k)
  filter_upwards [hall] with path hpath
  simp_rw [hpath]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => ConfigurationHistory.vertexMass rule state k path) n]

end
end Universality.Rule
