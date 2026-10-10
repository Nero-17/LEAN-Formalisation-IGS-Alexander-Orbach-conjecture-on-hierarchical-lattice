import IGSIII.Mass.ThreeStateMassPerron
import IGSIII.Mass.HistoryPathLaw

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter Matrix
open scoped Topology

/-- The actual retained connected-edge population has a strictly positive
Perron limit on the same independent innovation sample. -/
theorem marked_connected_population_positive_limit {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
      ∃ limit : ℝ, 0 < limit ∧
        Tendsto (fun depth => ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 limit) := by
  obtain ⟨right, left, coefficient, limit, _, _, _, left_positive, _, _, _, _, _, _, _,
    limit_positive, coordinate_convergence, _⟩ := classicalRule.three_state_mass_perron p positive below_one fixed_point
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have properties := limit_positive.and coordinate_convergence
  rw [← independentInnovationLaw_history_path rule p positive below_one fixed_point [] true] at properties
  have actual := ae_of_ae_map (markedHistoryPath_measurable rule [] true).aemeasurable properties
  filter_upwards [actual] with marks properties
  refine ⟨(spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
    (limit (markedHistoryPath rule [] true marks) * left .connected),
    mul_pos radius_positive (mul_pos properties.1 (left_positive .connected)), ?_⟩
  have shifted := ((properties.2 .connected).comp (tendsto_add_atTop_nat 1)).const_mul
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
  convert shifted using 1
  ext depth
  simp only [Function.comp_apply, Rule.ConfigurationHistory.rootLevelPopulation_succ,
    Rule.ConfigurationHistory.weightedPopulation,
    markedHistoryPath, Rule.ConfigurationHistory.latest_ofFine, FiniteNetwork.liveResponse_eq,
    mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, mul_zero, pow_succ]
  field_simp

end IGSIII.Chemical.Substitution
