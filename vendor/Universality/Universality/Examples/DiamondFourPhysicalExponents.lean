import Universality.Percolation.PhysicalExponentDefinition
import Universality.Examples.DiamondNumericalBounds

namespace Universality
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Rule
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

instance diamondRule_interior_nonempty : Nonempty diamondRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [diamondRule.network.card_interior_vertices]
  have := diamondRule_classical.vertices_gt_two
  omega

instance diamondRule_edges_neZero : NeZero diamondRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt diamondRule_classical.edges_gt_one)⟩

theorem diamond_four_physical_exponents :
    diamondRule.HasCriticalExponents diamondRule_classical.edges_gt_one diamondCriticalProbability
      (Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) /
        Real.log (6 - 2 * Real.sqrt 5))
      (Real.log 2 / Real.log (6 - 2 * Real.sqrt 5))
      (Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) /
        Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))))
      (4 - 2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2) := by
  have hm : 0 < 7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) := by
    have := diamond_mass_thermal_rational_bounds.1
    linarith
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have heta : 2 + Real.log (4 : ℝ) / Real.log 2 -
      2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2 =
      4 - 2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2 := by
    rw [hfour, mul_div_cancel_right₀ _ hlog]
    ring
  have hh := diamondRule_classical.hasCriticalExponents diamondCriticalProbability
    diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point
  change diamondRule.HasCriticalExponents _ _
    ((Real.log (4 : ℝ) - Real.log ((spectralRadius ℂ
      ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal)) /
      Real.log (deriv diamondNetwork.reliability diamondCriticalProbability))
    (Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target : ℝ) /
      Real.log (deriv diamondNetwork.reliability diamondCriticalProbability))
    (Real.log ((spectralRadius ℂ ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal) /
      (Real.log (4 : ℝ) - Real.log ((spectralRadius ℂ
        ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal)))
    (2 + Real.log (4 : ℝ) / Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target : ℝ) -
      2 * Real.log ((spectralRadius ℂ ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal) /
        Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target : ℝ)) at hh
  simpa only [diamond_critical_spectralRadius, ENNReal.toReal_ofReal hm.le,
    diamond_terminal_distance, Nat.cast_ofNat, diamond_critical_response,
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hm.ne', heta] using hh

theorem diamond_four_exponent_decimal_bounds :
    (16465 / 100000 : ℝ) ≤ Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) / Real.log (6 - 2 * Real.sqrt 5) ∧
    Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) / Real.log (6 - 2 * Real.sqrt 5) ≤ 16475 / 100000 ∧
    (163525 / 100000 : ℝ) ≤ Real.log 2 / Real.log (6 - 2 * Real.sqrt 5) ∧
    Real.log 2 / Real.log (6 - 2 * Real.sqrt 5) ≤ 163535 / 100000 ∧
    (1885845 / 100000 : ℝ) ≤ Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) /
      Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) ∧
    Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) /
      Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) ≤ 1885855 / 100000 ∧
    (20135 / 100000 : ℝ) ≤ 4 - 2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2 ∧
    4 - 2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2 ≤ 20145 / 100000 := by
  obtain ⟨h2L, h2U, htL, htU, hrL, hrU⟩ := diamond_logarithm_rational_bounds
  have h2 : 0 < Real.log (2 : ℝ) := by linarith
  have ht : 0 < Real.log (6 - 2 * Real.sqrt 5) := by linarith
  have hr : 0 < Real.log (4 / (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5))) := by linarith
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
  refine ⟨(le_div_iff₀ ht).mpr (by nlinarith), (div_le_iff₀ ht).mpr (by nlinarith),
    (le_div_iff₀ ht).mpr (by nlinarith), (div_le_iff₀ ht).mpr (by nlinarith),
    (le_div_iff₀ hr).mpr ?_, (div_le_iff₀ hr).mpr ?_, ?_, ?_⟩
  · rw [hmass]
    nlinarith
  · rw [hmass]
    nlinarith
  · have he := (div_le_iff₀ h2).mpr (show
        2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) ≤
          (4 - 20135 / 100000) * Real.log 2 by rw [hmass]; nlinarith)
    linarith
  · have he := (le_div_iff₀ h2).mpr (show
        (4 - 20145 / 100000) * Real.log 2 ≤
          2 * Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) by rw [hmass]; nlinarith)
    linarith

end
end Universality
