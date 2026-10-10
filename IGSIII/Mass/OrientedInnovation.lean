import IGSIII.Mass.OrientedVariance
import IGSIII.Mass.PopulationAlmostSure

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork Matrix MeasureTheory
open scoped BigOperators

/-- Four-type weighted population read directly from the latest graph. -/
noncomputable def orientedWeightedPopulation (rule : Rule) (state : LiveState)
    (values : MassLiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) : ℝ :=
  (rule.generation n).network.orientedResponse true (state == .both) (latest rule n history) values

noncomputable def orientedPopulationInnovation (rule : Rule) (p : ℝ) (state : LiveState)
    (values : MassLiveState → ℝ) (n : ℕ) (next : rule.ConfigurationHistory (n + 1)) : ℝ :=
  orientedWeightedPopulation rule state values (n + 1) next -
    orientedWeightedPopulation rule state (rule.network.orientedMassMatrix p *ᵥ values) n next.1

theorem orientedPopulationInnovation_eq_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (state : LiveState) (values : MassLiveState → ℝ) (n : ℕ) :
    (fun path => orientedPopulationInnovation rule p state values n (path (n + 1)))
      =ᵐ[infiniteLaw rule p positive below_one fixed_point (state == .connected)] fun path =>
        orientedWeightedPopulation rule state values (n + 1) (path (n + 1)) -
          orientedWeightedPopulation rule state (rule.network.orientedMassMatrix p *ᵥ values) n (path n) := by
  filter_upwards [infiniteLaw_extends rule p positive below_one fixed_point (state == .connected)] with path coherent
  unfold orientedPopulationInnovation
  rw [coherent n]

theorem refinementWeight_orientedPopulationInnovation_sq_le (rule : Rule) (p : ℝ)
    (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (state : LiveState) (values : MassLiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    (∑ fine, refinementWeight rule p n (latest rule n history) fine *
      orientedPopulationInnovation rule p state values n (history, fine) ^ 2) ≤
      weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n history := by
  classical
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    (∏ edge, rule.network.conditionalCellWeight p (latest rule n history edge)
      (substitutionConfigurationEquiv.symm fine edge)) *
    (((rule.generation n).network.substitute rule.network).orientedResponse true (state == .both) fine values -
      (rule.generation n).network.orientedResponse true (state == .both) (latest rule n history)
        (rule.network.orientedMassMatrix p *ᵥ values)) ^ 2) ≤ _
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  exact (rule.generation n).network.refinement_orientedResponse_variance_le rule.network p
    positive.le below_one.le (by rwa [fixed_point]) (by rwa [fixed_point])
    (latest rule n history) state values

theorem integral_orientedPopulationInnovation_sq_le (rule : Rule) (p : ℝ)
    (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (state : LiveState) (values : MassLiveState → ℝ) (n : ℕ) :
    (∫ path, orientedPopulationInnovation rule p state values n (path (n + 1)) ^ 2
      ∂infiniteLaw rule p positive below_one fixed_point (state == .connected)) ≤
      ∫ path, weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n (path n)
        ∂infiniteLaw rule p positive below_one fixed_point (state == .connected) := by
  rw [← integral_refinement_observable rule p positive below_one fixed_point (state == .connected) n
    (fun next => orientedPopulationInnovation rule p state values n next ^ 2)]
  apply integral_mono
    (integrable_infiniteLaw_observable rule p positive below_one fixed_point (state == .connected) n
      (fun history => ∑ fine, refinementWeight rule p n (latest rule n history) fine *
        orientedPopulationInnovation rule p state values n (history, fine) ^ 2))
    (integrable_infiniteLaw_observable rule p positive below_one fixed_point (state == .connected) n
      (fun history => weightedPopulation rule state (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) n history))
  intro path
  exact refinementWeight_orientedPopulationInnovation_sq_le rule p positive below_one fixed_point
    state values n (path n)

end Universality.Rule.ConfigurationHistory

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The genuine four-type innovation has geometric second-moment growth,
with the Perron root already identified from the actual three-type matrix. -/
theorem Classical.oriented_population_innovation_second_moment_bound {rule : Rule}
    (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (values : MassLiveState → ℝ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, ConfigurationHistory.orientedPopulationInnovation rule p state values n (path (n + 1)) ^ 2
        ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) ≤
          bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
  obtain ⟨bound, bound_positive, estimate⟩ := classicalRule.population_moment_bound p positive below_one fixed_point
    (fun _ => (rule.edges * ∑ child, |values child|) ^ 2) (fun _ => sq_nonneg _) 1
  refine ⟨bound, bound_positive, fun n state => ?_⟩
  apply (ConfigurationHistory.integral_orientedPopulationInnovation_sq_le rule p positive below_one fixed_point
    state values n).trans
  simpa only [pow_one, one_mul] using estimate n state

/-- Perron-normalized innovations vanish along every sufficiently large
generation almost surely, without passing to a subsequence. -/
theorem Classical.oriented_population_innovation_ae_zero {rule : Rule}
    (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (values : MassLiveState → ℝ) (state : LiveState) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n => ConfigurationHistory.orientedPopulationInnovation rule p state values n (path (n + 1)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 0) := by
  obtain ⟨bound, bound_positive, estimate⟩ := classicalRule.oriented_population_innovation_second_moment_bound
    p positive below_one fixed_point values
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have sums := IGSIII.Mass.ae_normalized_sum_zero_of_second_moment_bound
    (probability := ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected))
    (fun n path => ConfigurationHistory.orientedPopulationInnovation rule p state values n (path (n + 1)))
    (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
      (state == .connected) (n + 1) (ConfigurationHistory.orientedPopulationInnovation rule p state values n) 2)
    bound ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    bound_positive.le radius_gt_one (fun n => estimate n state)
  filter_upwards [sums] with path convergence
  have shifted := (convergence.comp (tendsto_add_atTop_nat 1)).const_mul
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
  have difference := shifted.sub convergence
  simp only [mul_zero, sub_zero] at difference
  convert difference using 1
  ext n
  simp only [Function.comp_apply]
  rw [Finset.sum_range_succ, pow_succ]
  field_simp [(zero_lt_one.trans radius_gt_one).ne']
  ring

end Universality.Rule
