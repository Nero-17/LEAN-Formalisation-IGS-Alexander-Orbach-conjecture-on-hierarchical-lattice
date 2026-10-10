import IGSIII4.CorePopulationMean
import IGSIII4.CoreGeometry
import IGSIII4.IntegralCoreClock
import IGSIII4.ActualChemicalData
import IGSIII.Chemical.SubstitutionPaths.CommonPrefixL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII34.Percolation

theorem terminalCoreEdges_card_positive {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
    0 < (terminalCoreEdges network configuration).card := by
  by_contra fails
  have empty : terminalCoreEdges network configuration = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos fails)
  have closed : terminalCoreConfiguration network configuration = fun _ => false := by
    funext edge
    simp [terminalCoreConfiguration, configurationOfPath, empty]
  have coreCrossing := terminalCoreConfiguration_crosses network simple configuration crossing
  rw [closed, network.crosses_all_closed] at coreCrossing
  contradiction

theorem marked_finite_observable_integrable (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (depth : ℕ)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    Integrable (fun marks => response (markedGenerationConfiguration rule marks depth [] true))
      (independentInnovationLaw rule probability positive belowOne fixedPoint) :=
  (marked_observable_memLp rule probability positive belowOne fixedPoint depth [] true response 1).integrable le_rfl

theorem terminalCoreMean_positive (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) :
    0 < terminalCoreMean rule.network probability := by
  classical
  have allOpenCrossing : rule.network.crosses (fun _ => true) = true :=
    (rule.network.crosses_eq_true _).mpr (classicalRule.connected _)
  have weightPositive : 0 < rule.network.conditionalCellWeight probability true (fun _ => true) := by
    simp only [conditionalCellWeight, allOpenCrossing, if_pos rfl, Bool.true_eq, ite_true, fixedPoint]
    exact div_pos (bernoulliWeight_pos positive belowOne (fun _ => true)) positive
  apply Finset.sum_pos' (fun configuration _ => mul_nonneg
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le _ _) (Nat.cast_nonneg _))
  exact ⟨fun _ => true, Finset.mem_univ _, mul_pos weightPositive
    (by exact_mod_cast terminalCoreEdges_card_positive rule.network classicalRule.simple _ allOpenCrossing)⟩

theorem marked_distance_integral (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (depth : ℕ) :
    (∫ marks, (((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth [] true)).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
      manuscriptDistanceMean rule probability (depth + 1) := by
  exact independentInnovationLaw_marked_observable rule probability positive belowOne fixedPoint depth [] true
    (fun configuration => (((rule.generation depth).network.openGraph configuration).dist
      (rule.generation depth).network.source (rule.generation depth).network.target : ℝ))

theorem actual_core_clock_mean_bound (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (pruning : AcceptedCorePruningSectionThree rule) (depth : ℕ) :
    manuscriptDistanceMean rule probability (depth + 1) ^ 2 ≤
      terminalCoreMean rule.network probability ^ (depth + 1) *
        ∫ marks, unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true)
          ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
  have meanPositive := pow_pos (terminalCoreMean_positive rule classicalRule probability positive belowOne fixedPoint) (depth + 1)
  rw [← generation_core_count_integral rule classicalRule probability positive belowOne fixedPoint depth] at meanPositive
  have bound := integral_sq_le_product_of_pointwise_square_bound
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => (((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth [] true)).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ))
    (fun marks => ((terminalCoreEdges (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)).card : ℝ))
    (fun marks => unitConfigurationResistance (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true))
    (marked_finite_observable_integrable rule probability positive belowOne fixedPoint depth
      (fun configuration => (((rule.generation depth).network.openGraph configuration).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ)))
    (marked_finite_observable_integrable rule probability positive belowOne fixedPoint depth
      (fun configuration => ((terminalCoreEdges (rule.generation depth).network configuration).card : ℝ)))
    (marked_finite_observable_integrable rule probability positive belowOne fixedPoint depth
      (fun configuration => unitConfigurationResistance (rule.generation depth).network configuration))
    (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Filter.Eventually.of_forall fun _ => (IGSIII34.Percolation.network _ _).effectiveResistance_nonnegative_all
      (fun _ => zero_le_one)) meanPositive
    (show ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      _ from by
      filter_upwards [independentInnovationLaw_crosses rule probability positive belowOne fixedPoint] with marks crossing
      exact terminalCore_distance_sq_le_count_mul_resistance (rule.generation depth).network
        (classicalRule.generation depth).simple _
        (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
        (pruning.resistancePreserved depth _ (markedGenerationConfiguration_crosses rule marks crossing depth [] true)))
  rwa [marked_distance_integral, generation_core_count_integral rule classicalRule probability positive belowOne fixedPoint] at bound

/-- The upper mean sandwich from Section 3, Lemma electrical-sandwich.
The field contains no core or chemical comparison. -/
structure AcceptedResistanceMeanUpperSectionThree (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint) where
  constant : ℝ
  constantPositive : 0 < constant
  meanUpper : ∀ depth,
    (∫ marks, unitConfigurationResistance (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) ≤ constant * accepted.growth ^ (depth + 1)

theorem actual_core_growth_clock (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (upper : AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint accepted)
    (pruning : AcceptedCorePruningSectionThree rule)
    (chemical : ActualChemicalSectionTwo rule probability positive belowOne fixedPoint) :
    chemical.growth ^ 2 ≤ terminalCoreMean rule.network probability * accepted.growth := by
  obtain ⟨constant, constantPositive, means⟩ := chemical.meanBounds
  have corePositive := terminalCoreMean_positive rule classicalRule probability positive belowOne fixedPoint
  have electricalPositive := zero_lt_one.trans accepted.growthAboveOne
  have chemicalPositive : 0 < chemical.growth := lt_of_lt_of_le
    (by exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale) chemical.growthLower
  have powerBound (depth : ℕ) : (chemical.growth ^ 2) ^ (depth + 1) ≤
      upper.constant * (terminalCoreMean rule.network probability * accepted.growth) ^ (depth + 1) := by
    have squareBound := mul_self_le_mul_self (pow_nonneg chemicalPositive.le _) (means (depth + 1)).1
    have bound := (actual_core_clock_mean_bound rule classicalRule probability positive belowOne fixedPoint pruning depth).trans
      (mul_le_mul_of_nonneg_left (upper.meanUpper depth) (pow_nonneg corePositive.le _))
    calc
      _ = (chemical.growth ^ (depth + 1)) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ manuscriptDistanceMean rule probability (depth + 1) ^ 2 := by simpa only [pow_two] using squareBound
      _ ≤ _ := by simpa only [mul_pow, mul_left_comm, mul_assoc] using bound
  by_contra failure
  have ratioAboveOne : 1 < chemical.growth ^ 2 / (terminalCoreMean rule.network probability * accepted.growth) :=
    (one_lt_div (mul_pos corePositive electricalPositive)).mpr (lt_of_not_ge failure)
  have ratioBound (depth : ℕ) : (chemical.growth ^ 2 / (terminalCoreMean rule.network probability * accepted.growth)) ^ (depth + 1) ≤ upper.constant := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos (mul_pos corePositive electricalPositive) _)).mpr (by simpa only [mul_comm] using powerBound depth)
  obtain ⟨depth, tooLarge⟩ := pow_unbounded_of_one_lt (max (1 : ℝ) upper.constant) ratioAboveOne
  have increasing : (chemical.growth ^ 2 / (terminalCoreMean rule.network probability * accepted.growth)) ^ depth ≤
      (chemical.growth ^ 2 / (terminalCoreMean rule.network probability * accepted.growth)) ^ (depth + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (zero_lt_one.trans ratioAboveOne).le depth) ratioAboveOne.le
  exact (not_lt_of_ge ((increasing.trans (ratioBound depth)).trans (le_max_right _ _))) tooLarge

end
end IGSIII4
