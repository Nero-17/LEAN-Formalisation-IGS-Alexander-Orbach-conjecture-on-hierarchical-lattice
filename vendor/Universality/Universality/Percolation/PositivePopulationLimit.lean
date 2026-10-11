import Universality.Percolation.PopulationLimitMean

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

/-- A specified positive Perron weight, rather than merely some existential
choice of eigenvector, admits a nonzero L² population limit. -/
theorem Classical.positive_population_L2_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 < values state)
    (heigen : rule.network.massMatrix p *ᵥ values =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • values)
    (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_trans zero_lt_one ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hmart := ConfigurationHistory.normalized_population_martingale rule p hp hp' hfixed symmetry hs ht
    values _ hradius.ne' heigen state
  obtain ⟨firstBound, hfirstBound, hfirst⟩ :=
    h.normalized_population_moment_bound p hp hp' hfixed values (fun s => (hvalues s).le) 1
  obtain ⟨fourthBound, hfourthBound, hfourth⟩ :=
    h.normalized_population_moment_bound p hp hp' hfixed values (fun s => (hvalues s).le) 4
  have hlimit := nonnegative_martingale_tendsto_L2 _ Filtration.piLE hmart
    (fun n path => div_nonneg
      ((rule.generation n).network.liveResponse_nonneg state _ values (fun s => (hvalues s).le))
      (pow_nonneg hradius.le n))
    (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => ConfigurationHistory.weightedPopulation rule state values n history /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) 2)
    (fun n => ConfigurationHistory.integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => (ConfigurationHistory.weightedPopulation rule state values n history /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ 4))
    firstBound fourthBound hfirstBound.le hfourthBound.le
    (fun n => by simpa only [pow_one] using hfirst n state) (fun n => hfourth n state)
  obtain ⟨limit, hlimit, _, hconv⟩ := hlimit
  refine ⟨limit, hlimit, ?_, hconv⟩
  rw [ConfigurationHistory.population_L2_limit_mean rule p hp hp' hfixed symmetry hs ht values _
    hradius.ne' heigen state limit hlimit hconv]
  exact mul_pos hradius (hvalues state)

end
end Universality.Rule
