import Universality.Percolation.PopulationConvergence

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

theorem integral_weightedPopulation_zero (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) (values : LiveState → ℝ) :
    (∫ path, weightedPopulation rule state values 0 (path 0)
      ∂infiniteLaw rule p hp hp' hfixed (state == .connected)) =
        (rule.network.massMatrix p *ᵥ values) state := by
  rw [integral_infiniteLaw rule p hp hp' hfixed (state == .connected) 0
    (weightedPopulation rule state values 0)]
  change (∑ fine, rule.network.conditionalCellWeight p (state == .connected) fine *
    rule.network.liveResponse state fine values) = _
  rw [rule.network.massMatrix_mulVec_response, rule.network.conditionalResponse_eq_weighted]

theorem population_L2_limit_mean (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (values : LiveState → ℝ) (radius : ℝ) (hradius : radius ≠ 0)
    (heigen : rule.network.massMatrix p *ᵥ values = radius • values) (state : LiveState)
    (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (hlimit : MemLp limit 2 (infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (hconv : Tendsto (fun n => eLpNorm
      ((fun path => weightedPopulation rule state values n (path n) / radius ^ n) - limit)
      2 (infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0)) :
    (∫ path, limit path ∂infiniteLaw rule p hp hp' hfixed (state == .connected)) = radius * values state := by
  rw [martingale_L2_limit_integral _ Filtration.piLE
    (normalized_population_martingale rule p hp hp' hfixed symmetry hs ht values radius hradius heigen state)
    limit hlimit hconv]
  simp only [pow_zero, div_one]
  rw [integral_weightedPopulation_zero, heigen]
  rfl

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

theorem Classical.exists_nonzero_population_L2_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ values : LiveState → ℝ, (∀ state, 0 < values state) ∧ ∀ state,
      ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
        MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
        0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
        (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
          Tendsto (fun n => ConfigurationHistory.weightedPopulation rule state values n (path n) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (limit path))) ∧
        Tendsto (fun n => eLpNorm
          ((fun path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
          2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨values, hvalues, heigen, hlimits⟩ := h.exists_population_L2_limit p hp hp' hfixed
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_trans zero_lt_one ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  refine ⟨values, hvalues, fun state => ?_⟩
  obtain ⟨limit, hlimit, hae, hconv⟩ := hlimits state
  refine ⟨limit, hlimit, ?_, hae, hconv⟩
  rw [ConfigurationHistory.population_L2_limit_mean rule p hp hp' hfixed symmetry hs ht values _
    hradius.ne' heigen state limit hlimit hconv]
  exact mul_pos hradius (hvalues state)

end
end Universality.Rule
