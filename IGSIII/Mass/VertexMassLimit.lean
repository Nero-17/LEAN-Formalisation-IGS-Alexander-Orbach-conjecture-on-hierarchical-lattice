import IGSIII.Mass.VertexPerronAlmostSure
import Universality.Percolation.VertexMassConvergence

set_option autoImplicit false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

/-- Retain both convergence modes and the positive mean for a specified
positive Perron weight of the actual configuration process. -/
theorem Classical.positive_population_ae_L2_limit {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (values : LiveState → ℝ) (values_positive : ∀ state, 0 < values state)
    (eigenvector : rule.network.massMatrix p *ᵥ values =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • values)
    (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
        Tendsto (fun n => ConfigurationHistory.weightedPopulation rule state values n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 (limit path))) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.weightedPopulation rule state values n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
      classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have martingale := ConfigurationHistory.normalized_population_martingale rule p positive below_one fixed_point
    symmetry source_swap target_swap values _ radius_positive.ne' eigenvector state
  obtain ⟨first_bound, first_positive, first_estimate⟩ :=
    classicalRule.normalized_population_moment_bound p positive below_one fixed_point values
      (fun state => (values_positive state).le) 1
  obtain ⟨fourth_bound, fourth_positive, fourth_estimate⟩ :=
    classicalRule.normalized_population_moment_bound p positive below_one fixed_point values
      (fun state => (values_positive state).le) 4
  obtain ⟨limit, limit_mem, convergence_ae, convergence_L2⟩ :=
    nonnegative_martingale_tendsto_L2 _ Filtration.piLE martingale
      (fun n path => div_nonneg
        ((rule.generation n).network.liveResponse_nonneg state _ values
          (fun state => (values_positive state).le)) (pow_nonneg radius_positive.le n))
      (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
        (state == .connected) n (fun history => ConfigurationHistory.weightedPopulation rule state values n history /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) 2)
      (fun n => ConfigurationHistory.integrable_infiniteLaw_observable rule p positive below_one fixed_point
        (state == .connected) n (fun history => (ConfigurationHistory.weightedPopulation rule state values n history /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ 4))
      first_bound fourth_bound first_positive.le fourth_positive.le
      (fun n => by simpa only [pow_one] using first_estimate n state) (fun n => fourth_estimate n state)
  refine ⟨limit, limit_mem, convergence_ae, ?_, convergence_L2⟩
  rw [ConfigurationHistory.population_L2_limit_mean rule p positive below_one fixed_point
    symmetry source_swap target_swap values _ radius_positive.ne' eigenvector state limit limit_mem convergence_L2]
  exact mul_pos radius_positive (values_positive state)

/-- The actual normalized internal vertex mass converges almost surely along
the whole sequence and in L² to the same limit, whose mean is strictly positive.
This concerns the three-state observable of II; no four-state identification or
almost-sure strict positivity is silently included. -/
theorem Classical.internal_vertex_mass_ae_L2_limit {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
        Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 (limit path))) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected))) atTop (𝓝 0) := by
  let probability := ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have radius_gt_one : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  obtain ⟨perron, remainder, eigenvalue, perron_positive, reward_split,
      perron_eigenvector, remainder_eigenvector, spectral_gap⟩ :=
    classicalRule.vertex_reward_spectral_split p positive below_one
  obtain ⟨limit, limit_mem, population_ae, positive_mean, population_L2⟩ :=
    classicalRule.positive_population_ae_L2_limit p positive below_one fixed_point
      perron perron_positive perron_eigenvector state
  refine ⟨(radius - 1)⁻¹ • limit, limit_mem.const_smul _, ?_, ?_, ?_⟩
  · have approximation := classicalRule.vertex_mass_perron_approximation_ae p positive below_one fixed_point
      perron remainder eigenvalue reward_split perron_eigenvector remainder_eigenvector spectral_gap state
    filter_upwards [approximation, population_ae] with path error_limit population_limit
    change Tendsto _ atTop (𝓝 ((radius - 1)⁻¹ * limit path))
    have combined := error_limit.add (population_limit.const_mul (radius - 1)⁻¹)
    simp only [zero_add] at combined
    convert combined using 1
    ext n
    change ConfigurationHistory.vertexMass rule state n path / radius ^ n = _
    change _ = (ConfigurationHistory.vertexMass rule state n path -
      ConfigurationHistory.weightedPopulation rule state perron n (path n) / (radius - 1)) / radius ^ n +
      (radius - 1)⁻¹ * (ConfigurationHistory.weightedPopulation rule state perron n (path n) / radius ^ n)
    ring
  · change 0 < ∫ path, (radius - 1)⁻¹ * limit path ∂probability
    rw [integral_const_mul]
    exact mul_pos (inv_pos.mpr (sub_pos.mpr radius_gt_one)) positive_mean
  · let population (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
      ConfigurationHistory.weightedPopulation rule state perron n (path n)
    have population_mem (n : ℕ) : MemLp (population n) 2 probability :=
      ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
        (state == .connected) n (ConfigurationHistory.weightedPopulation rule state perron n) 2
    let error (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
      (ConfigurationHistory.vertexMass rule state n path - population n path / (radius - 1)) / radius ^ n
    have error_measurable (n : ℕ) : AEStronglyMeasurable (error n) probability :=
      (memLp_div_const_real ((ConfigurationHistory.memLp_vertexMass rule p positive below_one fixed_point state n 2).sub
        (memLp_div_const_real (population_mem n) (radius - 1))) (radius ^ n)).aestronglyMeasurable
    have error_L2 : Tendsto (fun n => eLpNorm (error n) 2 probability) atTop (𝓝 0) :=
      classicalRule.vertex_mass_perron_approximation p positive below_one fixed_point perron remainder eigenvalue
        reward_split perron_eigenvector remainder_eigenvector spectral_gap state
    let difference (n : ℕ) := (fun path => population n path / radius ^ n) - limit
    have difference_measurable (n : ℕ) : AEStronglyMeasurable ((radius - 1)⁻¹ • difference n) probability :=
      (((memLp_div_const_real (population_mem n) (radius ^ n)).sub limit_mem).const_smul _).aestronglyMeasurable
    have scaled := L2_zero_smul (μ := probability) difference (radius - 1)⁻¹ population_L2
    have combined := L2_zero_add (μ := probability) error (fun n => (radius - 1)⁻¹ • difference n)
      error_measurable difference_measurable error_L2 scaled
    have identity (n : ℕ) : error n + (radius - 1)⁻¹ • difference n =
        (fun path => ConfigurationHistory.vertexMass rule state n path / radius ^ n) - (radius - 1)⁻¹ • limit := by
      funext path
      change error n path + (radius - 1)⁻¹ * (population n path / radius ^ n - limit path) =
        ConfigurationHistory.vertexMass rule state n path / radius ^ n - (radius - 1)⁻¹ * limit path
      dsimp [error]
      ring
    exact combined.congr' (Eventually.of_forall (fun n =>
      congrArg (fun function : (Π k, rule.ConfigurationHistory k) → ℝ => eLpNorm function 2 probability) (identity n)))

end Universality.Rule
