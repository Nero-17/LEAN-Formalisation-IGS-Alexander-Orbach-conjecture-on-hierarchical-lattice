import IGSIII.Mass.PopulationAlmostSure
import Universality.Percolation.SubcriticalPopulation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Mass

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

/-- A subcritical eigen-observable itself vanishes almost surely, as follows
by taking consecutive differences of its normalized accumulated sums. -/
theorem ae_subcritical_recursion_zero
    (population : ℕ → Ω → ℝ) (square_integrable : ∀ n, MemLp (population n) 2 probability)
    (eigenvalue bound radius : ℝ) (bound_nonnegative : 0 ≤ bound) (radius_gt_one : 1 < radius)
    (spectral_gap : |eigenvalue| < radius)
    (innovation_bound : ∀ n, ∫ sample, (population (n + 1) sample - eigenvalue * population n sample) ^ 2
      ∂probability ≤ bound * radius ^ n) :
    ∀ᵐ sample ∂probability,
      Tendsto (fun n => population n sample / radius ^ n) atTop (𝓝 0) := by
  have sums := ae_subcritical_recursion_sum_zero population square_integrable eigenvalue bound radius
    bound_nonnegative radius_gt_one spectral_gap innovation_bound
  filter_upwards [sums] with sample convergence
  have shifted := (convergence.comp (tendsto_add_atTop_nat 1)).const_mul radius
  have difference := shifted.sub convergence
  simp only [mul_zero, sub_zero] at difference
  convert difference using 1
  ext n
  simp only [Function.comp_apply]
  rw [Finset.sum_range_succ, pow_succ]
  field_simp [(zero_lt_one.trans radius_gt_one).ne']
  ring

end IGSIII.Mass

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- Every actual sub-Perron eigen-observable of the graph population vanishes
almost surely after Perron normalization. -/
theorem Classical.subcritical_population_ae_zero {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (values : LiveState → ℝ) (eigenvalue : ℝ)
    (eigenvector : rule.network.massMatrix p *ᵥ values = eigenvalue • values)
    (spectral_gap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n : ℕ => ConfigurationHistory.weightedPopulation rule state values n (path n) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 0) := by
  obtain ⟨bound, bound_positive, estimate⟩ := classicalRule.eigenpopulation_innovation_bound
    p positive below_one fixed_point values eigenvalue eigenvector
  exact IGSIII.Mass.ae_subcritical_recursion_zero
    (probability := ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected))
    (fun n path => ConfigurationHistory.weightedPopulation rule state values n (path n))
    (fun n => ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
      (state == .connected) n (ConfigurationHistory.weightedPopulation rule state values n) 2)
    eigenvalue bound ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) bound_positive.le
    ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
    spectral_gap (fun n => estimate n state)

end Universality.Rule
