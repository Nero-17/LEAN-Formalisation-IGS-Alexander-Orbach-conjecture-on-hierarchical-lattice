import Universality.Percolation.SubcriticalPopulation

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem Classical.subcritical_population_sum_L2_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (eigenvalue : ℝ)
    (heigen : rule.network.massMatrix p *ᵥ values = eigenvalue • values)
    (hgap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) :
    Tendsto (fun n : ℕ => eLpNorm (fun path =>
      (∑ k ∈ Finset.range n, ConfigurationHistory.weightedPopulation rule state values k (path k)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨bound, hbound, hestimate⟩ := h.eigenpopulation_innovation_bound p hp hp' hfixed values eigenvalue heigen
  exact subcritical_L2_recursion_sum_tendsto_zero
    (μ := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))
    (fun n path => ConfigurationHistory.weightedPopulation rule state values n (path n))
    (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected)
      n (ConfigurationHistory.weightedPopulation rule state values n) 2)
    eigenvalue bound ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) hbound.le
    ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
    hgap (fun n => hestimate n state)

end
end Universality.Rule
