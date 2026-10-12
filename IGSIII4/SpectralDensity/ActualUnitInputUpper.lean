import IGSIII4.SpectralDensity.ActualMomentCellComparison
import IGSIII4.SpectralDensity.ActualBinomialBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability Filter Topology
attribute [local instance] Classical.propDecidable

private theorem unit_chainWeight_nonnegative (blocks paths length : ℕ) (probability : ℝ)
    (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (configuration : Fin blocks → Fin paths → Configuration length) :
    0 ≤ chainWeight blocks paths length probability configuration := by
  apply Finset.prod_nonneg
  intro block _
  apply Finset.prod_nonneg
  intro path _
  exact bernoulliWeight_nonneg nonnegative atMostOne _

private theorem unit_critical_long_only_coefficient (blocks paths interior : ℕ) (probability : ℝ)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    (1 - probability ^ 2) * probability ^ 2 * (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks =
      probability * (1 - probability) := by
  rw [reliability_formula] at fixedPoint
  nlinarith [fixedPoint]

theorem blockInputResponse_unit {Outcome : Type*} (paths length : ℕ)
    (success : Configuration paths) (input : Fin paths → Fin length → Outcome) :
    blockInputResponse success (fun _ => (1 : ℝ)) input =
      (length : ℝ) / (successCount paths success : ℝ) := by
  have conductance : (∑ path, if success path = true then (length : ℝ)⁻¹ else 0) =
      successfulPathCount success * (length : ℝ)⁻¹ := by
    unfold successfulPathCount
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro path _
    split_ifs <;> ring
  simp only [blockInputResponse, parallelBlockResponse, pathInputResistance,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [conductance, mul_inv_rev, inv_inv, successfulPathCount_cast]
  rfl

theorem actualBlock_unit_mean {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (paths length : ℕ) (probability : ℝ) (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) :
    actualBlockObservable paths length probability weight (fun _ => 1) id =
      (length : ℝ) * finiteMean (conditionalStatusWeight paths (probability ^ length))
        (fun success => 1 / (successCount paths success : ℝ)) := by
  unfold actualBlockObservable
  simp_rw [blockInputResponse_unit, id_eq,
    finiteMean_const _ (blockProductWeight_normalized weight normalized)]
  rw [conditional_actual_block_status_law paths length probability (fun success => (length : ℝ) / (successCount paths success : ℝ))]
  simp only [div_eq_mul_inv, one_mul]
  exact finiteMean_const_mul _ _ _

theorem maskedCircuitMoment_short_unit {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (configuration : CircuitConfiguration blocks paths interior)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) (short : OuterShort configuration.1) :
    maskedCircuitMoment blocks paths interior configuration weight (fun _ => 1) id ≤ 2 := by
  have crossing : outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := Or.inl short
  simp only [maskedCircuitMoment, crossing, ↓reduceIte]
  rw [← finiteMean_const (productWeight (Edge := Fin 4) weight) (sum_productWeight weight normalized) (2 : ℝ)]
  apply finiteMean_mono _ (productWeight_nonnegative weight nonnegative)
  intro outer
  rw [← finiteMean_const (productWeight (Edge := Fin blocks) (blockProductWeight (length := interior + 2) (Path := Fin paths) weight))
    (sum_productWeight _ (blockProductWeight_normalized weight normalized)) (2 : ℝ)]
  apply finiteMean_mono _ (fun input => productWeight_nonnegative _ (fun input =>
    productWeight_nonnegative _ (fun input => productWeight_nonnegative weight nonnegative input) input) input)
  intro inner
  have upper := circuitVoltage_le_short (splitTyped configuration)
    (fun _ => (1 : ℝ)) (fun _ => by norm_num) short
  simpa only [circuitObservable, id_eq, shortResistance, one_add_one_eq_two] using upper

theorem maskedCircuitMoment_unit_upper {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (configuration : CircuitConfiguration blocks paths interior)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) :
    maskedCircuitMoment blocks paths interior configuration weight (fun _ => 1) id ≤
      (if OuterShort configuration.1 then 2 else 0) +
      (if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
        rawLongObservable blocks paths (interior + 2) configuration.2 weight (fun _ => 1) id else 0) := by
  by_cases short : OuterShort configuration.1
  · have failed : ¬OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := fun h => h.1 short
    simp only [short, failed, ↓reduceIte, add_zero]
    exact maskedCircuitMoment_short_unit blocks paths interior configuration weight nonnegative normalized short
  · by_cases long : OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1
    · simp only [short, long, ↓reduceIte, zero_add]
      exact (maskedCircuitMoment_long_only configuration weight (fun _ => 1) id long).le
    · have failed : ¬outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := by
        intro crossing
        rcases crossing with s | l
        · exact short s
        · exact long ⟨short, l⟩
      simp only [short, long, failed, maskedCircuitMoment, ↓reduceIte, add_zero, le_refl]

theorem weightedCell_unit_mean_upper {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths interior : ℕ) (probability : ℝ) (positive : 0 < probability)
    (atMostOne : probability ≤ 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (crossingPositive : 0 < 1 - (1 - probability ^ (interior + 2)) ^ paths)
    (weight : Outcome → ℝ) (nonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1) :
    weightedCellMean blocks paths interior probability weight (fun _ => 1) ≤
      2 * probability + (1 - probability) * (2 + (blocks : ℝ) * (interior + 2 : ℕ) *
        finiteMean (conditionalStatusWeight paths (probability ^ (interior + 2)))
          (fun success => 1 / (successCount paths success : ℝ))) := by
  unfold weightedCellMean
  rw [weightedCellObservable_split blocks paths interior probability fixedPoint weight (fun _ => 1) (fun _ => by norm_num) id]
  apply (div_le_iff₀ positive).mpr
  have comparison :
      (∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            maskedCircuitMoment blocks paths interior (outer,configuration) weight (fun _ => 1) id)) ≤
      ∑ configuration : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability configuration *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            (if OuterShort outer then 2 else 0) +
              (if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration) outer then
                rawLongObservable blocks paths (interior + 2) configuration weight (fun _ => 1) id else 0)) := by
    apply Finset.sum_le_sum
    intro configuration _
    apply mul_le_mul_of_nonneg_left _ (unit_chainWeight_nonnegative blocks paths (interior + 2) probability positive.le atMostOne configuration)
    exact finiteMean_mono (bernoulliWeight probability) (bernoulliWeight_nonneg positive.le atMostOne)
      (fun outer => maskedCircuitMoment_unit_upper blocks paths interior (outer, configuration) weight nonnegative normalized)
  have shortExpectation : Universality.FiniteNetwork.expectation probability (fun outer : Configuration 4 => if OuterShort outer then 2 else 0) =
      2 * probability ^ 2 := by
    have identity : (fun outer : Configuration 4 => if OuterShort outer then (2 : ℝ) else 0) =
        (fun outer => 2 * (if OuterShort outer then 1 else 0)) := by funext outer; split_ifs <;> ring
    rw [identity, Universality.FiniteNetwork.expectation_const_mul, outer_short_probability]
  simp only [Universality.FiniteNetwork.expectation_add, shortExpectation, mul_add, Finset.sum_add_distrib] at comparison
  rw [← Finset.sum_mul, chain_weight_normalization, one_mul,
    actual_long_only_observable blocks paths (interior + 2) probability crossingPositive weight (fun _ => 1) normalized id,
    unit_critical_long_only_coefficient blocks paths interior probability fixedPoint] at comparison
  have meanOne : finiteMean weight (fun _ => (1 : ℝ)) = 1 := finiteMean_const weight normalized 1
  simp only [id_eq] at comparison
  rw [actualLong_mean blocks paths (interior + 2) probability crossingPositive weight (fun _ => 1) normalized meanOne,
    actualBlock_unit_mean paths (interior + 2) probability weight normalized] at comparison
  convert comparison using 1 <;> first | rfl | ring

/-- The unit-input upper estimate is derived from the actual conditioned finite
cell law at the family's own critical points. -/
theorem appendix_weightedCell_unit_mean_upper {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (base : ℝ) (baseAboveOne : 1 < base) (weight : Outcome → ℝ)
    (nonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1) :
    ∀ᶠ length : ℕ in atTop,
      weightedCellMean (blockCount base length) (pathCount length) (length - 2)
        (appendixCriticalProbability base length) weight (fun _ => 1) ≤
          (2 + 8 / Real.log base) * (blockCount base length : ℝ) := by
  filter_upwards [appendix_conditional_inverse_upper_eventually base baseAboveOne,
    appendixCriticalProbability_interval_eventually base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length inverseBound interval lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have blockCrossing := critical_block_crossing_lower (blockCount base length) (pathCount length) (length - 2)
    blocksPositive _ interval.1 interval.2 fixedPoint
  simp only [Nat.sub_add_cancel lengthLarge] at blockCrossing
  have crossingPositive : 0 < 1 - (1 - appendixCriticalProbability base length ^ length) ^ pathCount length := by linarith
  have upper := weightedCell_unit_mean_upper (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) positive belowOne.le fixedPoint
    (by simpa only [Nat.sub_add_cancel lengthLarge] using crossingPositive) weight nonnegative normalized
  simp only [Nat.sub_add_cancel lengthLarge] at upper
  have inverseNonnegative : 0 ≤ finiteMean
      (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
      (fun success => 1 / (successCount (pathCount length) success : ℝ)) := by
    apply Finset.sum_nonneg
    intro success _
    apply mul_nonneg
    · exact conditionalStatusWeight_nonnegative (pathCount length) _ (pow_nonneg positive.le length)
        (pow_le_one₀ positive.le belowOne.le) crossingPositive success
    · positivity
  have scaledNonnegative : 0 ≤ (blockCount base length : ℝ) * (length : ℝ) * finiteMean
      (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
      (fun success => 1 / (successCount (pathCount length) success : ℝ)) := by positivity
  have blocksAtLeastOne : (1 : ℝ) ≤ (blockCount base length : ℝ) := by exact_mod_cast blocksPositive
  calc
    _ ≤ 2 + (blockCount base length : ℝ) * ((length : ℝ) * finiteMean
        (conditionalStatusWeight (pathCount length) (appendixCriticalProbability base length ^ length))
        (fun success => 1 / (successCount (pathCount length) success : ℝ))) := by
      nlinarith [mul_nonneg positive.le scaledNonnegative]
    _ ≤ 2 + (blockCount base length : ℝ) * (8 / Real.log base) :=
      by
      have scaled := mul_le_mul_of_nonneg_left inverseBound.le (show 0 ≤ (blockCount base length : ℝ) by positivity)
      linarith
    _ ≤ (2 + 8 / Real.log base) * (blockCount base length : ℝ) := by nlinarith

end
end IGSIII4.SpectralDensity.ActualFamily

