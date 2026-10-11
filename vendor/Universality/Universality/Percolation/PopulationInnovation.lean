import Universality.Percolation.RefinementPopulationVariance
import Universality.Percolation.PopulationSquareBound

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix MeasureTheory
open scoped BigOperators

def populationInnovation (rule : Rule) (p : ℝ) (state : LiveState) (values : LiveState → ℝ)
    (n : ℕ) (next : rule.ConfigurationHistory (n + 1)) : ℝ :=
  weightedPopulation rule state values (n + 1) next -
    weightedPopulation rule state (rule.network.massMatrix p *ᵥ values) n next.1

theorem populationInnovation_eq_ae (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) (values : LiveState → ℝ) (n : ℕ) :
    (fun path => populationInnovation rule p state values n (path (n + 1)))
      =ᵐ[infiniteLaw rule p hp hp' hfixed (state == .connected)] fun path =>
        weightedPopulation rule state values (n + 1) (path (n + 1)) -
          weightedPopulation rule state (rule.network.massMatrix p *ᵥ values) n (path n) := by
  filter_upwards [infiniteLaw_extends rule p hp hp' hfixed (state == .connected)] with path hpath
  unfold populationInnovation
  rw [hpath n]

theorem refinementWeight_populationInnovation_sq_le (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (state : LiveState) (values : LiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    (∑ fine, refinementWeight rule p n (latest rule n history) fine *
      populationInnovation rule p state values n (history, fine) ^ 2) ≤
      weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n history := by
  classical
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    (∏ e, rule.network.conditionalCellWeight p (latest rule n history e)
      (substitutionConfigurationEquiv.symm fine e)) *
    (((rule.generation n).network.substitute rule.network).liveResponse state fine values -
      (rule.generation n).network.liveResponse state (latest rule n history) (rule.network.massMatrix p *ᵥ values)) ^ 2) ≤ _
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  exact (rule.generation n).network.refinement_liveResponse_variance_le rule.network p hp.le hp'.le
    (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht (latest rule n history) state values

theorem integral_populationInnovation_sq_le (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (state : LiveState) (values : LiveState → ℝ) (n : ℕ) :
    (∫ path, populationInnovation rule p state values n (path (n + 1)) ^ 2
      ∂infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
      ∫ path, weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n (path n)
        ∂infiniteLaw rule p hp hp' hfixed (state == .connected) := by
  rw [← integral_refinement_observable rule p hp hp' hfixed (state == .connected) n
    (fun next => populationInnovation rule p state values n next ^ 2)]
  apply integral_mono
    (integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => ∑ fine, refinementWeight rule p n (latest rule n history) fine *
        populationInnovation rule p state values n (history, fine) ^ 2))
    (integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n history))
  intro path
  exact refinementWeight_populationInnovation_sq_le rule p hp hp' hfixed symmetry hs ht state values n (path n)

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory

theorem Classical.population_innovation_second_moment_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, ConfigurationHistory.populationInnovation rule p state values n (path (n + 1)) ^ 2
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
          bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
  obtain ⟨bound, hbound, hestimate⟩ := h.population_moment_bound p hp hp' hfixed
    (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) (fun _ => sq_nonneg _) 1
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  refine ⟨bound, hbound, fun n state => ?_⟩
  apply (ConfigurationHistory.integral_populationInnovation_sq_le rule p hp hp' hfixed symmetry hs ht state values n).trans
  simpa only [pow_one, one_mul] using hestimate n state

end
end Universality.Rule
