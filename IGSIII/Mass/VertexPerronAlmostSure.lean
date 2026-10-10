import IGSIII.Mass.VertexRewardAlmostSure
import IGSIII.Mass.PopulationAlmostSure
import Universality.Percolation.VertexMassPerronApproximation

set_option autoImplicit false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual internal vertex mass is approximated by the Perron population
almost surely along the entire sequence. All three random error terms are
controlled by the actual innovation moment bounds. -/
theorem Classical.vertex_mass_perron_approximation_ae {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (perron remainder : LiveState → ℝ) (eigenvalue : ℝ)
    (reward_split : rule.network.conditionalVertexMass p = perron + remainder)
    (perron_eigenvector : rule.network.massMatrix p *ᵥ perron =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • perron)
    (remainder_eigenvector : rule.network.massMatrix p *ᵥ remainder = eigenvalue • remainder)
    (spectral_gap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n : ℕ =>
        (ConfigurationHistory.vertexMass rule state n path -
          ConfigurationHistory.weightedPopulation rule state perron n (path n) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1)) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 0) := by
  let probability := ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let population (values : LiveState → ℝ) (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    ConfigurationHistory.weightedPopulation rule state values n (path n)
  have radius_gt_one : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have population_mem (values : LiveState → ℝ) (n : ℕ) : MemLp (population values n) 2 probability :=
    ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
      (state == .connected) n (ConfigurationHistory.weightedPopulation rule state values n) 2
  obtain ⟨remainder_bound, remainder_bound_positive, remainder_estimate⟩ :=
    classicalRule.eigenpopulation_innovation_bound p positive below_one fixed_point
      remainder eigenvalue remainder_eigenvector
  have remainder_zero := IGSIII.Mass.ae_subcritical_recursion_sum_zero
    (probability := probability) (population remainder) (population_mem remainder)
    eigenvalue remainder_bound radius remainder_bound_positive.le radius_gt_one spectral_gap
    (fun n => remainder_estimate n state)
  obtain ⟨perron_bound, perron_bound_positive, perron_estimate⟩ :=
    classicalRule.eigenpopulation_innovation_bound p positive below_one fixed_point
      perron radius perron_eigenvector
  have perron_zero := IGSIII.Mass.ae_perron_sum_remainder_zero
    (probability := probability) (population perron) (population_mem perron)
    perron_bound radius perron_bound_positive.le radius_gt_one (fun n => perron_estimate n state)
  have reward_zero := classicalRule.vertex_reward_compensation_ae_zero p positive below_one fixed_point state
  filter_upwards [reward_zero, remainder_zero, perron_zero] with path reward_limit remainder_limit perron_limit
  have initial_zero : Tendsto (fun n => ConfigurationHistory.vertexMass rule state 0 path / radius ^ n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |radius⁻¹| < 1 by
          rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans radius_gt_one))]
          exact inv_lt_one_of_one_lt₀ radius_gt_one)).const_mul
        (ConfigurationHistory.vertexMass rule state 0 path : ℝ)
  have combined := ((reward_limit.add initial_zero).add remainder_limit).add perron_limit
  simp only [add_zero] at combined
  convert combined using 1
  ext n
  change (ConfigurationHistory.vertexMass rule state n path - population perron n path / (radius - 1)) / radius ^ n =
    ((ConfigurationHistory.vertexMass rule state n path - ConfigurationHistory.vertexMass rule state 0 path -
      ∑ k ∈ Finset.range n, population (rule.network.conditionalVertexMass p) k path) / radius ^ n +
      ConfigurationHistory.vertexMass rule state 0 path / radius ^ n) +
      (∑ k ∈ Finset.range n, population remainder k path) / radius ^ n +
      ((∑ k ∈ Finset.range n, population perron k path) - population perron n path / (radius - 1)) / radius ^ n
  have split_population (k : ℕ) : population (rule.network.conditionalVertexMass p) k path =
      population perron k path + population remainder k path := by
    rw [reward_split]
    exact ConfigurationHistory.weightedPopulation_add rule state perron remainder k (path k)
  simp_rw [split_population, Finset.sum_add_distrib]
  ring

end Universality.Rule
