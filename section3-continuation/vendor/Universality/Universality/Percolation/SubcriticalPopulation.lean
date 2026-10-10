import Universality.Percolation.PopulationInnovation
import Universality.Probability.SubcriticalL2Recursion

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 400000
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem ConfigurationHistory.weightedPopulation_smul (rule : Rule) (state : LiveState)
    (values : LiveState → ℝ) (scale : ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    weightedPopulation rule state (scale • values) n history =
      scale * weightedPopulation rule state values n history :=
  (rule.generation n).network.liveResponse_smul state (latest rule n history) values scale

theorem Classical.eigenpopulation_innovation_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (eigenvalue : ℝ)
    (heigen : rule.network.massMatrix p *ᵥ values = eigenvalue • values) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, (ConfigurationHistory.weightedPopulation rule state values (n + 1) (path (n + 1)) -
        eigenvalue * ConfigurationHistory.weightedPopulation rule state values n (path n)) ^ 2
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
        bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
  obtain ⟨bound, hbound, hestimate⟩ := h.population_innovation_second_moment_bound p hp hp' hfixed values
  refine ⟨bound, hbound, fun n state => ?_⟩
  have heq : (∫ path, (ConfigurationHistory.weightedPopulation rule state values (n + 1) (path (n + 1)) -
      eigenvalue * ConfigurationHistory.weightedPopulation rule state values n (path n)) ^ 2
      ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) =
      ∫ path, ConfigurationHistory.populationInnovation rule p state values n (path (n + 1)) ^ 2
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected) := by
    apply integral_congr_ae
    filter_upwards [ConfigurationHistory.populationInnovation_eq_ae rule p hp hp' hfixed state values n]
      with path hpath
    rw [hpath, heigen, ConfigurationHistory.weightedPopulation_smul]
  rw [heq]
  exact hestimate n state

/-- Every actual population eigen-observable with strictly sub-Perron
eigenvalue vanishes in L² at the genuine mass-growth scale. -/
theorem Classical.subcritical_population_L2_zero {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (eigenvalue : ℝ)
    (heigen : rule.network.massMatrix p *ᵥ values = eigenvalue • values)
    (hgap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) :
    Tendsto (fun n : ℕ => eLpNorm (fun path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨bound, hbound, hestimate⟩ := h.eigenpopulation_innovation_bound p hp hp' hfixed values eigenvalue heigen
  exact subcritical_L2_recursion_tendsto_zero
    (μ := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))
    (fun n path => ConfigurationHistory.weightedPopulation rule state values n (path n))
    (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected)
      n (ConfigurationHistory.weightedPopulation rule state values n) 2)
    eigenvalue bound ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) hbound.le
    ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1) hgap
    (fun n => hestimate n state)

end
end Universality.Rule
