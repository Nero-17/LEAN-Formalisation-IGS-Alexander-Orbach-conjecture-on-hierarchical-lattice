import IGSIII4.SpectralDensity.ActualMomentEventLaw
import IGSIII34.Resistance.FiniteElectricalVariance

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable
variable {blocks paths interior : ℕ}

theorem circuitVoltage_nonnegative (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    0 ≤ circuitVoltage configuration resistance := by
  have shortPositive : 0 < shortResistance resistance := add_pos (positive (.inl 0)) (positive (.inl 1))
  have longPositive := longResistance_positive configuration resistance positive
  unfold circuitVoltage shortConductance longConductance
  split_ifs <;> positivity

theorem circuitVoltage_le_short (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (short : ShortCrosses configuration) :
    circuitVoltage configuration resistance ≤ shortResistance resistance := by
  have shortPositive : 0 < shortResistance resistance := add_pos (positive (.inl 0)) (positive (.inl 1))
  have longPositive := longResistance_positive configuration resistance positive
  have comparison : (shortResistance resistance)⁻¹ ≤ shortConductance configuration resistance + longConductance configuration resistance := by
    simp only [shortConductance, short, ↓reduceIte]
    apply le_add_of_nonneg_right
    unfold longConductance
    split_ifs <;> positivity
  simpa only [one_div, inv_inv, circuitVoltage] using
    one_div_le_one_div_of_le (inv_pos.mpr shortPositive) comparison

theorem split_blockResistance {Outcome : Type*}
    (configuration : CircuitConfiguration blocks paths interior)
    (input : CircuitInput blocks paths interior Outcome) (response : Outcome → ℝ) (block : Fin blocks) :
    blockResistance (splitTyped configuration) (fun edge => response (splitTyped input edge)) block =
      blockInputResponse (pathStatuses paths (interior + 2) (configuration.2 block)) response (input.2 block) := by
  simp only [blockResistance, blockConductance, pathConductance, pathResistance, splitTyped,
    blockInputResponse, parallelBlockResponse, pathInputResistance, pathStatuses, pathCrossing, decide_eq_true_eq]

theorem split_longResistance {Outcome : Type*}
    (configuration : CircuitConfiguration blocks paths interior)
    (input : CircuitInput blocks paths interior Outcome) (response : Outcome → ℝ) :
    longResistance (splitTyped configuration) (fun edge => response (splitTyped input edge)) =
      (response (input.1 2) + response (input.1 3)) +
        ∑ block, blockInputResponse (pathStatuses paths (interior + 2) (configuration.2 block)) response (input.2 block) := by
  change response (input.1 2) + (∑ block, blockResistance (splitTyped configuration)
    (fun edge => response (splitTyped input edge)) block) + response (input.1 3) = _
  simp_rw [split_blockResistance configuration input response]
  ring

theorem circuitVoltage_long_only {Outcome : Type*}
    (configuration : CircuitConfiguration blocks paths interior)
    (input : CircuitInput blocks paths interior Outcome) (response : Outcome → ℝ)
    (long : OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1) :
    circuitVoltage (splitTyped configuration) (fun edge => response (splitTyped input edge)) =
      (response (input.1 2) + response (input.1 3)) +
        ∑ block, blockInputResponse (pathStatuses paths (interior + 2) (configuration.2 block)) response (input.2 block) := by
  have shortFailed : ¬ShortCrosses (splitTyped configuration) := long.1
  have longCross : LongCrosses (splitTyped configuration) := long.2
  simp only [circuitVoltage, shortConductance, shortFailed, ↓reduceIte, zero_add,
    longConductance, longCross, inv_inv]
  exact split_longResistance configuration input response

theorem finiteMean_short_pair_second {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean (fun input : Outcome × Outcome => weight input.1 * weight input.2)
      (fun input => (response input.1 + response input.2) ^ 2) ≤ 20 := by
  have mean : finiteMean (fun input : Outcome × Outcome => weight input.1 * weight input.2)
      (fun input => response input.1 + response input.2) = 2 := by
    rw [finiteMean_product weight weight (fun first second => response first + response second)]
    simp only [finiteMean_add, finiteMean_const weight normalized, meanOne]
    norm_num
  have variance := finiteVariance_product_add weight response weight response normalized normalized
  rw [finiteVariance_eq_second_moment _ _ (product_weight_normalized weight weight normalized normalized), mean] at variance
  nlinarith

def maskedCircuitMoment {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (configuration : CircuitConfiguration blocks paths interior)
    (weight response : Outcome → ℝ) (observable : ℝ → ℝ) : ℝ :=
  if outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
    finiteMean (productWeight weight) (fun outer : Fin 4 → Outcome =>
      finiteMean (productWeight (blockProductWeight weight))
        (fun inner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
          circuitObservable blocks paths interior configuration response observable (outer, inner)))
  else 0

theorem maskedCircuitMoment_long_only {Outcome : Type*} [Fintype Outcome]
    (configuration : CircuitConfiguration blocks paths interior) (weight response : Outcome → ℝ)
    (observable : ℝ → ℝ)
    (long : OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1) :
    maskedCircuitMoment blocks paths interior configuration weight response observable =
      rawLongObservable blocks paths (interior + 2) configuration.2 weight response observable := by
  have crossing : outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := Or.inr long.2
  simp only [maskedCircuitMoment, crossing, ↓reduceIte, circuitObservable, circuitVoltage_long_only configuration _ response long,
    rawLongObservable]

theorem maskedCircuitMoment_nonnegative {Outcome : Type*} [Fintype Outcome]
    (configuration : CircuitConfiguration blocks paths interior) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (positive : ∀ outcome, 0 < response outcome) :
    0 ≤ maskedCircuitMoment blocks paths interior configuration weight response id := by
  unfold maskedCircuitMoment
  split_ifs
  · apply Finset.sum_nonneg
    intro outer _
    apply mul_nonneg (productWeight_nonnegative weight weightNonnegative outer)
    apply Finset.sum_nonneg
    intro inner _
    apply mul_nonneg (productWeight_nonnegative _ (fun input =>
      productWeight_nonnegative _ (fun input => productWeight_nonnegative weight weightNonnegative input) input) inner)
    exact circuitVoltage_nonnegative _ _ (fun edge => positive _)
  · exact le_rfl

theorem maskedCircuitMoment_mean_lower {Outcome : Type*} [Fintype Outcome]
    (configuration : CircuitConfiguration blocks paths interior) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (positive : ∀ outcome, 0 < response outcome) :
    (if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
      rawLongObservable blocks paths (interior + 2) configuration.2 weight response id else 0) ≤
      maskedCircuitMoment blocks paths interior configuration weight response id := by
  split_ifs with long
  · exact (maskedCircuitMoment_long_only configuration weight response id long).ge
  · exact maskedCircuitMoment_nonnegative configuration weight response weightNonnegative positive

theorem maskedCircuitMoment_short_second {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (configuration : CircuitConfiguration blocks paths interior) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome, 0 < response outcome) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) (short : OuterShort configuration.1) :
    maskedCircuitMoment blocks paths interior configuration weight response (fun value => value ^ 2) ≤ 20 := by
  have crossing : outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := Or.inl short
  simp only [maskedCircuitMoment, crossing, ↓reduceIte]
  have comparison : finiteMean (productWeight weight) (fun outer : Fin 4 → Outcome =>
      finiteMean (productWeight (blockProductWeight weight))
        (fun inner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
          circuitObservable blocks paths interior configuration response (fun value => value ^ 2) (outer, inner))) ≤
      finiteMean (productWeight weight) (fun outer : Fin 4 → Outcome => (response (outer 0) + response (outer 1)) ^ 2) := by
    apply finiteMean_mono _ (productWeight_nonnegative weight weightNonnegative)
    intro outer
    rw [← finiteMean_const (productWeight (Edge := Fin blocks) (blockProductWeight (length := interior + 2) (Path := Fin paths) weight))
      (sum_productWeight _ (blockProductWeight_normalized weight normalized)) ((response (outer 0) + response (outer 1)) ^ 2)]
    apply finiteMean_mono _ (fun input => productWeight_nonnegative _ (fun input =>
      productWeight_nonnegative _ (fun input => productWeight_nonnegative weight weightNonnegative input) input) input)
    intro inner
    have upper := circuitVoltage_le_short (splitTyped configuration)
      (fun edge => response (splitTyped (outer, inner) edge)) (fun edge => positive _) short
    have lower := circuitVoltage_nonnegative (splitTyped configuration)
      (fun edge => response (splitTyped (outer, inner) edge)) (fun edge => positive _)
    change circuitVoltage (splitTyped configuration) (fun edge => response (splitTyped (outer, inner) edge)) ^ 2 ≤ _
    change _ ≤ response (outer 0) + response (outer 1) at upper
    nlinarith
  apply comparison.trans
  rw [finiteMean_four_shuffle weight (fun short _ => (response short.1 + response short.2) ^ 2)]
  simp only [finiteMean_const _ (product_weight_normalized weight weight normalized normalized)]
  exact finiteMean_short_pair_second weight response normalized meanOne varianceBound

theorem maskedCircuitMoment_second_upper {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (configuration : CircuitConfiguration blocks paths interior) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome, 0 < response outcome) (meanOne : finiteMean weight response = 1)
    (varianceBound : finiteVariance weight response ≤ 8) :
    maskedCircuitMoment blocks paths interior configuration weight response (fun value => value ^ 2) ≤
      (if OuterShort configuration.1 then 20 else 0) +
        (if OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
          rawLongObservable blocks paths (interior + 2) configuration.2 weight response (fun value => value ^ 2) else 0) := by
  by_cases short : OuterShort configuration.1
  · have failed : ¬OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := fun h => h.1 short
    simp only [short, failed, ↓reduceIte, add_zero]
    exact maskedCircuitMoment_short_second configuration weight response weightNonnegative normalized positive meanOne varianceBound short
  · by_cases long : OuterLongOnly (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1
    · simp only [short, long, ↓reduceIte, zero_add]
      exact (maskedCircuitMoment_long_only configuration weight response _ long).le
    · have crossingFailed : ¬outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 := by
        intro crossing
        rcases crossing with s | l
        · exact short s
        · exact long ⟨short,l⟩
      simp only [short, long, crossingFailed, maskedCircuitMoment, ↓reduceIte, add_zero, le_refl]

end
end IGSIII4.SpectralDensity.ActualFamily
