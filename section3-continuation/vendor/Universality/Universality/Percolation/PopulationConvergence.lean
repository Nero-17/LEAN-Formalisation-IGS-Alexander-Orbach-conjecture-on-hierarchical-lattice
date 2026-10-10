import Universality.Percolation.PopulationSquareBound
import Universality.Probability.FourthMomentConvergence

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

theorem Classical.normalized_population_moment_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 ≤ values state) (order : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, (ConfigurationHistory.weightedPopulation rule state values n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ order
          ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤ bound := by
  obtain ⟨bound, hbound, hestimate⟩ := h.population_moment_bound p hp hp' hfixed values hvalues order
  refine ⟨bound, hbound, fun n state => ?_⟩
  simp_rw [div_pow, ← pow_mul]
  rw [integral_div]
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_trans zero_lt_one ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  apply (div_le_iff₀ (pow_pos hradius _)).mpr
  simpa only [Nat.mul_comm n order] using hestimate n state

/-- The positive Perron-weighted population of the actual configuration
process converges almost surely and in L². This is a population limit; the
identification of the normalized accumulated vertex reward remains separate. -/
theorem Classical.exists_population_L2_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ values : LiveState → ℝ, (∀ state, 0 < values state) ∧
      rule.network.massMatrix p *ᵥ values =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • values ∧ ∀ state,
      ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
        MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
        (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
          Tendsto (fun n => ConfigurationHistory.weightedPopulation rule state values n (path n) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (limit path))) ∧
        Tendsto (fun n => eLpNorm
          ((fun path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
          2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨values, hvalues, heigen, hmartingale⟩ := h.exists_population_martingale p hp hp' hfixed
  obtain ⟨firstBound, hfirstBound, hfirst⟩ :=
    h.normalized_population_moment_bound p hp hp' hfixed values (fun s => (hvalues s).le) 1
  obtain ⟨fourthBound, hfourthBound, hfourth⟩ :=
    h.normalized_population_moment_bound p hp hp' hfixed values (fun s => (hvalues s).le) 4
  refine ⟨values, hvalues, heigen, fun state => ?_⟩
  apply nonnegative_martingale_tendsto_L2 _ Filtration.piLE (hmartingale state)
      ?_ ?_ ?_ firstBound fourthBound hfirstBound.le hfourthBound.le ?_ ?_
  · intro n path
    apply div_nonneg
    · exact (rule.generation n).network.liveResponse_nonneg state _ values (fun s => (hvalues s).le)
    · exact pow_nonneg ENNReal.toReal_nonneg _
  · intro n
    exact ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => ConfigurationHistory.weightedPopulation rule state values n history /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) 2
  · intro n
    exact ConfigurationHistory.integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => (ConfigurationHistory.weightedPopulation rule state values n history /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ 4)
  · intro n
    simpa only [pow_one] using hfirst n state
  · exact fun n => hfourth n state

end
end Universality.Rule
