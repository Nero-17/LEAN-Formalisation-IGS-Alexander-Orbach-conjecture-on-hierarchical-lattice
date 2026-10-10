import IGSIII34.Resistance.RandomComparison
import IGSIII34.Probability.FiniteProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge State : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [Fintype State]

theorem referenceCurrent_configuration_update_invariant (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : State → ℝ) (positive : ∀ value, 0 < resistance value)
    (changed : Edge) (configuration : Edge → State) (value : State) :
    network.referenceCurrent connected (fun edge => resistance (Function.update configuration changed value edge))
      (fun edge => positive _) changed =
    network.referenceCurrent connected (fun edge => resistance (configuration edge))
      (fun edge => positive _) changed := by
  have updateIdentity : (fun edge => resistance (Function.update configuration changed value edge)) =
      Function.update (fun edge => resistance (configuration edge)) changed (resistance value) := by
    funext edge
    by_cases same : edge = changed
    · subst edge
      simp
    · simp [Function.update_of_ne same]
  simp only [referenceCurrent, updateIdentity, Function.update_idem]

/-- The manuscript's graph-independent comparison for an arbitrary finite
joint law of a positive pair, sampled independently on the network's edges. -/
theorem finite_iid_resistance_comparison (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (weight : State → ℝ) (weightNonnegative : ∀ value, 0 ≤ weight value)
    (weightSum : ∑ value, weight value = 1) (base : State)
    (first second : State → ℝ)
    (firstPositive : ∀ value, 0 < first value) (secondPositive : ∀ value, 0 < second value) :
    Probability.expectation weight (fun configuration : Edge → State =>
      max (network.effectiveResistance (fun edge => first (configuration edge)) -
        network.effectiveResistance (fun edge => second (configuration edge))) 0) ≤
    ((∑ value, weight value * (max (first value - second value) 0 * max 1 ((second value)⁻¹ ^ 2))) /
      (∑ value, weight value * min (second value) (second value)⁻¹)) *
    Probability.expectation weight (fun configuration : Edge → State =>
      network.effectiveResistance (fun edge => second (configuration edge))) := by
  let numerator := ∑ value, weight value *
    (max (first value - second value) 0 * max 1 ((second value)⁻¹ ^ 2))
  let denominator := ∑ value, weight value * min (second value) (second value)⁻¹
  have numeratorNonnegative : 0 ≤ numerator :=
    Finset.sum_nonneg (fun value _ => mul_nonneg (weightNonnegative value)
      (mul_nonneg (le_max_right _ _) ((zero_le_one.trans (le_max_left _ _)))))
  have positiveWeight : ∃ value, 0 < weight value := by
    by_contra none
    have allZero (value : State) : weight value = 0 :=
      le_antisymm (le_of_not_gt (not_exists.mp none value)) (weightNonnegative value)
    simp only [allZero, Finset.sum_const_zero] at weightSum
    norm_num at weightSum
  obtain ⟨positiveValue, weightPositive⟩ := positiveWeight
  have denominatorPositive : 0 < denominator := by
    have termPositive : 0 < weight positiveValue *
        min (second positiveValue) (second positiveValue)⁻¹ :=
      mul_pos weightPositive (lt_min (secondPositive positiveValue)
        (inv_pos.mpr (secondPositive positiveValue)))
    exact termPositive.trans_le (Finset.single_le_sum
      (fun value _ => mul_nonneg (weightNonnegative value)
        (le_min (secondPositive value).le (inv_nonneg.mpr (secondPositive value).le)))
      (Finset.mem_univ positiveValue))
  have referenceInvariant (changed : Edge) (configuration : Edge → State) (value : State) :
      network.referenceCurrent connected
        (fun edge => second (Function.update configuration changed value edge)) (fun edge => secondPositive _) changed ^ 2 =
      network.referenceCurrent connected (fun edge => second (configuration edge))
        (fun edge => secondPositive _) changed ^ 2 := by
    rw [network.referenceCurrent_configuration_update_invariant connected second secondPositive]
  have upperBound (changed : Edge) :
      Probability.expectation weight (fun configuration : Edge → State =>
        max (first (configuration changed) - second (configuration changed)) 0 *
          network.minimizingCurrent connected (fun edge => second (configuration edge))
            (fun edge => secondPositive _) changed ^ 2) ≤
      numerator * Probability.expectation weight (fun configuration : Edge → State =>
        network.referenceCurrent connected (fun edge => second (configuration edge))
          (fun edge => secondPositive _) changed ^ 2) := by
    calc
      _ ≤ Probability.expectation weight (fun configuration : Edge → State =>
          (max (first (configuration changed) - second (configuration changed)) 0 *
            max 1 ((second (configuration changed))⁻¹ ^ 2)) *
              network.referenceCurrent connected (fun edge => second (configuration edge))
                (fun edge => secondPositive _) changed ^ 2) :=
        Probability.expectation_mono weight weightNonnegative (fun configuration =>
          network.reference_current_difference_upper_bound connected
            (fun edge => first (configuration edge)) (fun edge => second (configuration edge))
            (fun edge => secondPositive _) changed)
      _ = _ := Probability.expectation_coordinate_factorisation weight weightSum changed base
        (fun value => max (first value - second value) 0 * max 1 ((second value)⁻¹ ^ 2))
        (fun configuration => network.referenceCurrent connected
          (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed ^ 2)
        (referenceInvariant changed)
  have lowerBound (changed : Edge) :
      denominator * Probability.expectation weight (fun configuration : Edge → State =>
        network.referenceCurrent connected (fun edge => second (configuration edge))
          (fun edge => secondPositive _) changed ^ 2) ≤
      Probability.expectation weight (fun configuration : Edge → State =>
        second (configuration changed) *
          network.minimizingCurrent connected (fun edge => second (configuration edge))
            (fun edge => secondPositive _) changed ^ 2) := by
    calc
      _ = Probability.expectation weight (fun configuration : Edge → State =>
          min (second (configuration changed)) (second (configuration changed))⁻¹ *
            network.referenceCurrent connected (fun edge => second (configuration edge))
              (fun edge => secondPositive _) changed ^ 2) :=
        (Probability.expectation_coordinate_factorisation weight weightSum changed base
          (fun value => min (second value) (second value)⁻¹)
          (fun configuration => network.referenceCurrent connected
            (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed ^ 2)
          (referenceInvariant changed)).symm
      _ ≤ _ := Probability.expectation_mono weight weightNonnegative (fun configuration =>
        network.reference_current_weighted_lower_bound connected
          (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed)
  have edgeComparison (changed : Edge) :
      Probability.expectation weight (fun configuration : Edge → State =>
        max (first (configuration changed) - second (configuration changed)) 0 *
          network.minimizingCurrent connected (fun edge => second (configuration edge))
            (fun edge => secondPositive _) changed ^ 2) ≤
      (numerator / denominator) * Probability.expectation weight (fun configuration : Edge → State =>
        second (configuration changed) * network.minimizingCurrent connected
          (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed ^ 2) := by
    apply (upperBound changed).trans
    have dividedBound : Probability.expectation weight (fun configuration : Edge → State =>
        network.referenceCurrent connected (fun edge => second (configuration edge))
          (fun edge => secondPositive _) changed ^ 2) ≤
      Probability.expectation weight (fun configuration : Edge → State =>
        second (configuration changed) * network.minimizingCurrent connected
          (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed ^ 2) / denominator := by
      apply (le_div_iff₀ denominatorPositive).mpr
      simpa only [mul_comm] using lowerBound changed
    have multiplied := mul_le_mul_of_nonneg_left dividedBound numeratorNonnegative
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using multiplied
  have energyIdentity (configuration : Edge → State) :
      (∑ edge, second (configuration edge) * network.minimizingCurrent connected
        (fun edge => second (configuration edge)) (fun edge => secondPositive _) edge ^ 2) =
        network.effectiveResistance (fun edge => second (configuration edge)) :=
    network.minimizingCurrent_energy connected _ _
  calc
    _ ≤ Probability.expectation weight (fun configuration : Edge → State =>
        ∑ edge, max (first (configuration edge) - second (configuration edge)) 0 *
          network.minimizingCurrent connected (fun edge => second (configuration edge))
            (fun edge => secondPositive _) edge ^ 2) :=
      Probability.expectation_mono weight weightNonnegative (fun configuration =>
        network.effectiveResistance_positive_difference_le_trial_sum
          (fun edge => firstPositive _) (network.minimizingCurrent_unitFlow connected _ _)
          (network.minimizingCurrent_energy connected _ _))
    _ = _ := Probability.expectation_sum weight _
    _ ≤ ∑ changed, (numerator / denominator) *
        Probability.expectation weight (fun configuration : Edge → State =>
          second (configuration changed) * network.minimizingCurrent connected
            (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed ^ 2) :=
      Finset.sum_le_sum (fun changed _ => edgeComparison changed)
    _ = _ := by
      rw [← Finset.mul_sum, ← Probability.expectation_sum]
      simp only [energyIdentity, numerator, denominator]

end
end IGSIII34.Resistance.FiniteNetwork
