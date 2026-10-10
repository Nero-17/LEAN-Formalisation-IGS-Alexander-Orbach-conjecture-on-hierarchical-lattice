import Universality.Examples.DiamondFourPhysicalExponents
import Universality.Percolation.PhysicalMomentExponents

namespace Universality
noncomputable section
set_option maxHeartbeats 1000000
open Rule

/-- The manuscript's four-decimal diamond supercritical susceptibility value. -/
theorem diamond_susceptibility_exponent_decimal_bounds :
    (294115 / 100000 : ℝ) ≤
      (2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) - Real.log 4) /
        Real.log (6 - 2 * Real.sqrt 5) ∧
    (2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) - Real.log 4) /
        Real.log (6 - 2 * Real.sqrt 5) ≤ (294125 / 100000 : ℝ) := by
  obtain ⟨h2L, h2U, htL, htU, hrL, hrU⟩ := diamond_logarithm_rational_bounds
  have ht : 0 < Real.log (6 - 2 * Real.sqrt 5) := by linarith
  have hm : 0 < 7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) := by
    have := diamond_mass_thermal_rational_bounds.1
    linarith
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hmass : Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) =
      2 * Real.log 2 - Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hm.ne', hfour]
    ring
  rw [hmass, hfour]
  exact ⟨(le_div_iff₀ ht).mpr (by nlinarith), (div_le_iff₀ ht).mpr (by nlinarith)⟩

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- Equality d^2=m=4 makes the original diamond annealed susceptibility
infinite at every strictly positive subcritical parameter. -/
theorem diamond_physical_subcritical_susceptibility_eq_top (p : ℝ)
    (hp : 0 < p) (hpc : p < diamondCriticalProbability) :
    diamondRule.physicalFiniteClusterMoment diamondRule_classical.edges_gt_one p 1 = ⊤ := by
  have hdegree : diamondRule.network.fullGraph.degree diamondRule.network.source = 2 := by decide
  have hfinite := diamondRule_classical.physical_subcritical_moment_finite_iff
    diamondCriticalProbability p diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2
      diamond_critical_fixed_point hp hpc 1
  have hnot : ¬ (diamondRule.network.fullGraph.degree diamondRule.network.source : ℝ) ^ (1 + 1) <
      diamondRule.edges := by rw [hdegree]; norm_num [diamondRule]
  by_contra hne
  exact hnot (hfinite.mp hne)

end
end Universality
