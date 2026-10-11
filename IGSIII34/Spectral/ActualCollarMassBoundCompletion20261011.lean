import IGSIII34.Spectral.ActualCollarExpectationCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix IGSIII.Geometry
open scoped BigOperators

theorem actual_terminal_collar_envelope_integrable_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (fine coarseDepth collarDepth : ℕ) :
    Integrable (actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
      continuation fine coarseDepth collarDepth) (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  unfold actualTerminalCollarEnvelopeCompletion20261011
  apply integrable_finsetSum
  intro word _
  apply integrable_finsetSum
  intro side _
  apply integrable_finsetSum
  intro suffix _
  apply integrable_finsetSum
  intro parent _
  exact (actual_coarse_live_descendant_mass_product_completion20261011 rule p positive belowOne fixedPoint
    continuation (List.ofFn word) (List.ofFn suffix) parent).1

theorem actual_terminal_collar_envelope_integral_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (fine coarseDepth collarDepth : ℕ) :
    (∫ marks, actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
      continuation fine coarseDepth collarDepth marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
    (∑ parent : OrientedState, ∫ marks, continuation.mass parent marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) *
    (∑ side : Bool, (actualTerminalSocketSetCompletion20261011 rule fine collarDepth side).card : ℝ) *
    (∫ marks, (actualLiveComponentCountCompletion20261011 rule marks coarseDepth : ℝ)
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) := by
  classical
  have termIntegrable (word : Fin coarseDepth → (Fin rule.edges × Bool))
      (suffix : Fin collarDepth → Fin rule.edges) (parent : OrientedState) :=
    (actual_coarse_live_descendant_mass_product_completion20261011 rule p positive belowOne fixedPoint
      continuation (List.ofFn word) (List.ofFn suffix) parent).1
  have parentIntegrable (word : Fin coarseDepth → (Fin rule.edges × Bool))
      (suffix : Fin collarDepth → Fin rule.edges) :=
    integrable_finsetSum Finset.univ (fun parent _ => termIntegrable word suffix parent)
  have suffixIntegrable (word : Fin coarseDepth → (Fin rule.edges × Bool)) (side : Bool) :=
    integrable_finsetSum (actualTerminalSocketSetCompletion20261011 rule fine collarDepth side)
      (fun suffix _ => parentIntegrable word suffix)
  have sideIntegrable (word : Fin coarseDepth → (Fin rule.edges × Bool)) :=
    integrable_finsetSum Finset.univ (fun side _ => suffixIntegrable word side)
  unfold actualTerminalCollarEnvelopeCompletion20261011
  rw [integral_finsetSum Finset.univ (fun word _ => sideIntegrable word)]
  conv_lhs =>
    arg 2
    intro word
    rw [integral_finsetSum Finset.univ (fun side _ => suffixIntegrable word side)]
    arg 2
    intro side
    rw [integral_finsetSum (actualTerminalSocketSetCompletion20261011 rule fine collarDepth side)
      (fun suffix _ => parentIntegrable word suffix)]
    arg 2
    intro suffix
    rw [integral_finsetSum Finset.univ (fun parent _ => termIntegrable word suffix parent)]
  simp_rw [(actual_coarse_live_descendant_mass_product_completion20261011 rule p positive belowOne fixedPoint
    continuation _ _ _).2]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul]
  rw [← integral_finsetSum Finset.univ
    (fun word _ => actualLiveIndicator_integrable_completion20261011 rule (List.ofFn word) _)]
  have countEquality (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
      (∑ word : Fin coarseDepth → (Fin rule.edges × Bool),
        actualLiveIndicatorCompletion20261011 rule (List.ofFn word) marks) =
      (actualLiveComponentCountCompletion20261011 rule marks coarseDepth : ℝ) := by
    simp only [actualLiveComponentCountCompletion20261011, Finset.card_eq_sum_ones, Finset.sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, actualLiveIndicatorCompletion20261011]
  simp_rw [countEquality]
  ring

/-- The actual collar envelope has an annealed geometric bound, uniformly
in both the coarse generation and the fine generation used to recognise
physical socket incidences. This uses the actual critical population. -/
theorem actual_terminal_collar_envelope_Perron_bound_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ fine coarseDepth collarDepth : ℕ,
      (∫ marks, actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
        continuation fine coarseDepth collarDepth marks /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(coarseDepth + collarDepth)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      coefficient * ((rule.network.fullGraph.degree rule.network.source : ℝ) /
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^collarDepth := by
  classical
  obtain ⟨populationBound, populationPositive, populations⟩ :=
    actual_live_component_count_expectation_Perron_bound_completion20261011 rule classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have orientedCard : Fintype.card OrientedState = 5 := by decide
  refine ⟨10 * continuation.meanBound * populationBound,
    mul_pos (mul_pos (by norm_num) continuation.meanBoundPositive) populationPositive, ?_⟩
  intro fine coarseDepth collarDepth
  have meanBound : (∑ parent : OrientedState, ∫ marks, continuation.mass parent marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ 5 * continuation.meanBound := by
    calc
      _ ≤ ∑ _parent : OrientedState, continuation.meanBound := Finset.sum_le_sum (fun parent _ => continuation.means parent)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, orientedCard, nsmul_eq_mul, Nat.cast_ofNat]
  have socketBound : (∑ side : Bool,
      ((actualTerminalSocketSetCompletion20261011 rule fine collarDepth side).card : ℝ)) ≤
      2 * (rule.network.fullGraph.degree rule.network.source : ℝ)^collarDepth := by
    calc
      _ ≤ ∑ _side : Bool, (rule.network.fullGraph.degree rule.network.source : ℝ)^collarDepth := by
        apply Finset.sum_le_sum
        intro side _
        exact_mod_cast actual_terminal_socket_count_bound_completion20261011 rule classicalRule fine collarDepth side
      _ = _ := by simp
  have socketNonnegative : 0 ≤ ∑ side : Bool,
      ((actualTerminalSocketSetCompletion20261011 rule fine collarDepth side).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have populationNonnegative : 0 ≤ ∫ marks,
      (actualLiveComponentCountCompletion20261011 rule marks coarseDepth : ℝ)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
    integral_nonneg (fun _ => Nat.cast_nonneg _)
  have envelopeBound : (∫ marks, actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
      continuation fine coarseDepth collarDepth marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      (10 * continuation.meanBound * populationBound) *
        (rule.network.fullGraph.degree rule.network.source : ℝ)^collarDepth *
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^coarseDepth := by
    rw [actual_terminal_collar_envelope_integral_completion20261011]
    have productBound := mul_le_mul meanBound socketBound socketNonnegative
      (mul_nonneg (by norm_num) continuation.meanBoundPositive.le)
    have wholeBound := mul_le_mul productBound (populations coarseDepth) populationNonnegative
      (mul_nonneg (mul_nonneg (by norm_num) continuation.meanBoundPositive.le)
        (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)))
    convert wholeBound using 1
    all_goals first | rfl | ring
  rw [integral_div]
  calc
    _ ≤ ((10 * continuation.meanBound * populationBound) *
        (rule.network.fullGraph.degree rule.network.source : ℝ)^collarDepth *
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^coarseDepth) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(coarseDepth + collarDepth) :=
      div_le_div_of_nonneg_right envelopeBound (pow_nonneg radiusPositive.le _)
    _ = _ := by
      rw [pow_add, div_pow]
      field_simp

end
end IGSIII34.Spectral
