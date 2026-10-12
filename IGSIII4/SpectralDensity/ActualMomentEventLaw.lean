import IGSIII4.SpectralDensity.ActualMomentDisintegration
import IGSIII4.SpectralDensity.ActualMomentProductShuffle

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability
attribute [local instance] Classical.propDecidable

def OuterShort (configuration : Configuration 4) : Prop := configuration 0 = true ∧ configuration 1 = true

def OuterLongOnly (chainEvent : Prop) (configuration : Configuration 4) : Prop :=
  ¬OuterShort configuration ∧ configuration 2 = true ∧ configuration 3 = true ∧ chainEvent

theorem outer_short_probability (probability : ℝ) :
    Universality.FiniteNetwork.expectation probability (fun configuration : Configuration 4 =>
      if OuterShort configuration then 1 else 0) = probability ^ 2 := by
  have equal : (fun configuration : Configuration 4 => if OuterShort configuration then (1 : ℝ) else 0) =
      (fun configuration => if outerCrossing False configuration then 1 else 0) := by
    funext configuration
    simp [OuterShort, outerCrossing]
  rw [equal, outer_crossing_probability]
  simp

theorem outer_long_only_probability (probability : ℝ) (chainEvent : Prop) :
    Universality.FiniteNetwork.expectation probability (fun configuration : Configuration 4 =>
      if OuterLongOnly chainEvent configuration then 1 else 0) =
      (1 - probability ^ 2) * probability ^ 2 * (if chainEvent then 1 else 0) := by
  have pointwise (configuration : Configuration 4) :
      (if OuterLongOnly chainEvent configuration then (1 : ℝ) else 0) =
      (if outerCrossing chainEvent configuration then 1 else 0) - (if OuterShort configuration then 1 else 0) := by
    by_cases short : OuterShort configuration
    · have crossing : outerCrossing chainEvent configuration := Or.inl short
      simp [OuterLongOnly, short, crossing]
    · simp only [OuterLongOnly, short, not_false_eq_true, true_and, ↓reduceIte]
      simp only [outerCrossing, show ¬(configuration 0 = true ∧ configuration 1 = true) from short, false_or]
      split_ifs <;> ring
  simp_rw [pointwise]
  rw [Universality.FiniteNetwork.expectation_sub, outer_crossing_probability, outer_short_probability]
  ring

def conditionedLongObservable {Outcome : Type*} [Fintype Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ) (observable : ℝ → ℝ) : ℝ :=
  finiteMean (productWeight (conditionalActualBlockWeight paths length probability))
    (fun configuration : Fin blocks → Fin paths → Configuration length =>
      finiteMean (fun exterior : Outcome × Outcome => weight exterior.1 * weight exterior.2)
        (fun exterior => finiteMean (productWeight (blockProductWeight weight))
          (fun input : Fin blocks → Fin paths → Fin length → Outcome =>
            observable ((response exterior.1 + response exterior.2) +
              ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block)))))

theorem conditionedLongObservable_eq_actual {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ) (weight response : Outcome → ℝ) (observable : ℝ → ℝ) :
    conditionedLongObservable blocks paths length probability weight response observable =
      finiteMean (actualLongWeight blocks paths length probability weight)
        (fun input => observable (actualLongResponse blocks paths length response input)) := by
  unfold conditionedLongObservable
  rw [finiteMean_swap (productWeight (conditionalActualBlockWeight paths length probability))
    (fun exterior : Outcome × Outcome => weight exterior.1 * weight exterior.2)]
  have inner (exterior : Outcome × Outcome) :
      finiteMean (productWeight (conditionalActualBlockWeight paths length probability))
        (fun configuration : Fin blocks → Fin paths → Configuration length =>
          finiteMean (productWeight (blockProductWeight weight))
            (fun input : Fin blocks → Fin paths → Fin length → Outcome =>
              observable ((response exterior.1 + response exterior.2) +
                ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block)))) =
      finiteMean (productWeight (actualBlockJointWeight paths length probability weight))
        (fun input : Fin blocks → BlockSample paths length Outcome =>
          observable ((response exterior.1 + response exterior.2) +
            ∑ block, actualBlockSampleResponse paths length response (input block))) := by
    exact finiteMean_product_shuffle (conditionalActualBlockWeight paths length probability) (blockProductWeight weight)
      (fun configuration input => observable ((response exterior.1 + response exterior.2) +
        ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block)))
  simp only [inner]
  exact (finiteMean_product (fun exterior : Outcome × Outcome => weight exterior.1 * weight exterior.2)
    (productWeight (actualBlockJointWeight paths length probability weight))
    (fun exterior input => observable ((response exterior.1 + response exterior.2) +
      ∑ block, actualBlockSampleResponse paths length response (input block)))).symm

def rawLongObservable {Outcome : Type*} [Fintype Outcome] (blocks paths length : ℕ)
    (configuration : Fin blocks → Fin paths → Configuration length)
    (weight response : Outcome → ℝ) (observable : ℝ → ℝ) : ℝ :=
  finiteMean (productWeight weight) (fun exterior : Fin 4 → Outcome =>
    finiteMean (productWeight (blockProductWeight weight))
      (fun input : Fin blocks → Fin paths → Fin length → Outcome =>
        observable ((response (exterior 2) + response (exterior 3)) +
          ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block))))

theorem rawLongObservable_reduce {Outcome : Type*} [Fintype Outcome]
    (blocks paths length : ℕ) (configuration : Fin blocks → Fin paths → Configuration length)
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) (observable : ℝ → ℝ) :
    rawLongObservable blocks paths length configuration weight response observable =
      finiteMean (fun exterior : Outcome × Outcome => weight exterior.1 * weight exterior.2)
        (fun exterior => finiteMean (productWeight (blockProductWeight weight))
          (fun input : Fin blocks → Fin paths → Fin length → Outcome =>
            observable ((response exterior.1 + response exterior.2) +
              ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block)))) := by
  unfold rawLongObservable
  rw [finiteMean_four_shuffle weight
    (fun _ exterior => finiteMean (productWeight (blockProductWeight weight))
      (fun input : Fin blocks → Fin paths → Fin length → Outcome =>
        observable ((response exterior.1 + response exterior.2) +
          ∑ block, blockInputResponse (pathStatuses paths length (configuration block)) response (input block))))]
  exact finiteMean_const _ (product_weight_normalized weight weight normalized normalized) _

theorem raw_chain_masked_observable (blocks paths length : ℕ) (probability : ℝ)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (observable : (Fin blocks → Fin paths → Configuration length) → ℝ) :
    (∑ configuration, chainWeight blocks paths length probability configuration *
      (if chainCrossing blocks paths length configuration then observable configuration else 0)) =
      (1 - (1 - probability ^ length) ^ paths) ^ blocks *
        finiteMean (productWeight (conditionalActualBlockWeight paths length probability)) observable := by
  unfold finiteMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [conditionalActualChainWeight]
  by_cases crossing : chainCrossing blocks paths length configuration
  · simp only [crossing, ↓reduceIte]
    field_simp [ne_of_gt crossingPositive]
  · simp only [crossing, ↓reduceIte, zero_div, zero_mul, mul_zero]

theorem actual_long_only_observable {Outcome : Type*} [Fintype Outcome] [Nonempty Outcome]
    (blocks paths length : ℕ) (probability : ℝ)
    (crossingPositive : 0 < 1 - (1 - probability ^ length) ^ paths)
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) (observable : ℝ → ℝ) :
    (∑ configuration : Fin blocks → Fin paths → Configuration length,
      chainWeight blocks paths length probability configuration *
        Universality.FiniteNetwork.expectation probability (fun outer =>
          if OuterLongOnly (chainCrossing blocks paths length configuration) outer then
            rawLongObservable blocks paths length configuration weight response observable else 0)) =
    ((1 - probability ^ 2) * probability ^ 2 * (1 - (1 - probability ^ length) ^ paths) ^ blocks) *
      finiteMean (actualLongWeight blocks paths length probability weight)
        (fun input => observable (actualLongResponse blocks paths length response input)) := by
  have outer (configuration : Fin blocks → Fin paths → Configuration length) :
      Universality.FiniteNetwork.expectation probability (fun outer =>
        if OuterLongOnly (chainCrossing blocks paths length configuration) outer then
          rawLongObservable blocks paths length configuration weight response observable else 0) =
      ((1 - probability ^ 2) * probability ^ 2) *
        (if chainCrossing blocks paths length configuration then rawLongObservable blocks paths length configuration weight response observable else 0) := by
    have identity : (fun outer : Configuration 4 =>
        if OuterLongOnly (chainCrossing blocks paths length configuration) outer then
          rawLongObservable blocks paths length configuration weight response observable else 0) =
        (fun outer => (if OuterLongOnly (chainCrossing blocks paths length configuration) outer then 1 else 0) *
          rawLongObservable blocks paths length configuration weight response observable) := by
      funext outer; split_ifs <;> ring
    rw [identity, Universality.FiniteNetwork.expectation_mul_const, outer_long_only_probability]
    split_ifs <;> ring
  simp_rw [outer]
  have rearrange (configuration : Fin blocks → Fin paths → Configuration length) :
      chainWeight blocks paths length probability configuration * (((1 - probability ^ 2) * probability ^ 2) *
        (if chainCrossing blocks paths length configuration then rawLongObservable blocks paths length configuration weight response observable else 0)) =
      ((1 - probability ^ 2) * probability ^ 2) * (chainWeight blocks paths length probability configuration *
        (if chainCrossing blocks paths length configuration then rawLongObservable blocks paths length configuration weight response observable else 0)) := by ring
  simp_rw [rearrange]
  rw [← Finset.mul_sum, raw_chain_masked_observable blocks paths length probability crossingPositive]
  simp_rw [rawLongObservable_reduce blocks paths length _ weight response normalized observable]
  change _ * (_ * conditionedLongObservable blocks paths length probability weight response observable) = _
  rw [conditionedLongObservable_eq_actual]
  ring

end
end IGSIII4.SpectralDensity.ActualFamily
