import Universality.Percolation.RefinementMean
import Universality.Percolation.HistoryConditionalExpectation

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Perron-weighted live edges read from the actual graph configuration. -/
def weightedPopulation (rule : Rule) (state : LiveState) (values : LiveState → ℝ)
    (n : ℕ) (history : rule.ConfigurationHistory n) : ℝ :=
  (rule.generation n).network.liveResponse state (latest rule n history) values

theorem normalized_population_martingale (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (values : LiveState → ℝ) (radius : ℝ) (hradius : radius ≠ 0)
    (heigen : rule.network.massMatrix p *ᵥ values = radius • values)
    (state : LiveState) :
    Martingale (fun n path => weightedPopulation rule state values n (path n) / radius ^ n)
      Filtration.piLE (infiniteLaw rule p hp hp' hfixed (state == .connected)) := by
  apply martingale_nat
  · exact history_observables_stronglyAdapted rule
      (fun n history => weightedPopulation rule state values n history / radius ^ n)
  · intro n
    exact integrable_infiniteLaw_observable rule p hp hp' hfixed _ n
      (fun history => weightedPopulation rule state values n history / radius ^ n)
  · intro n
    apply Filter.EventuallyEq.symm
    apply (infiniteLaw_condExp rule p hp hp' hfixed (state == .connected) n
      (fun next => weightedPopulation rule state values (n + 1) next / radius ^ (n + 1))).trans
    apply Filter.Eventually.of_forall
    intro path
    change (∑ fine, refinementWeight rule p n (latest rule n (path n)) fine *
      ((rule.generation (n + 1)).network.liveResponse state fine values / radius ^ (n + 1))) =
      (rule.generation n).network.liveResponse state (latest rule n (path n)) values / radius ^ n
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    rw [refinementWeight_liveResponse rule p hp hp' hfixed symmetry hs ht,
      heigen, FiniteNetwork.liveResponse_smul, pow_succ]
    field_simp

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory ProbabilityTheory

/-- The actual normalized live population is a martingale with strictly
positive weights and the genuine mass spectral radius. -/
theorem Classical.exists_population_martingale {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ values : LiveState → ℝ, (∀ state, 0 < values state) ∧
      rule.network.massMatrix p *ᵥ values =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • values ∧ ∀ state,
      Martingale (fun n path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        Filtration.piLE (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hspectral : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
      ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  rw [hspectral]
  refine ⟨massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
    positiveRoot (massPlaneBlock (rule.network.massMatrix p)) - massPlaneBlock (rule.network.massMatrix p) 0 0],
    ?_, ?_, ?_⟩
  · apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]
  · intro state
    apply ConfigurationHistory.normalized_population_martingale rule p hp hp' hfixed symmetry hs ht
    · exact ne_of_gt (positiveRoot_pos _ hblock)
    · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]

end
end Universality.Rule
