import IGSIII34.Resistance.InputMeasurability
import IGSIII34.Probability.CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory ProbabilityTheory

attribute [local irreducible] effectiveResistance

variable {Vertex Edge State Outcome : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [MeasurableSpace State] [MeasurableSpace Outcome]

theorem independent_pair_resistance_integral_comparison
    (measure : Measure Outcome) [IsProbabilityMeasure measure]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (edgeInputs : Edge → Outcome → State) (independent : iIndepFun edgeInputs measure)
    (measurableEdgeInputs : ∀ edge, Measurable (edgeInputs edge)) (base : State)
    (first second : State → ℝ) (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (firstPositive : ∀ value, 0 < first value) (secondPositive : ∀ value, 0 < second value)
    (firstIntegrable : ∀ edge, Integrable (fun outcome => first (edgeInputs edge outcome)) measure)
    (secondIntegrable : ∀ edge, Integrable (fun outcome => second (edgeInputs edge outcome)) measure)
    (numeratorIntegrable : ∀ edge, Integrable (fun outcome =>
      max (first (edgeInputs edge outcome) - second (edgeInputs edge outcome)) 0 *
        max 1 ((second (edgeInputs edge outcome))⁻¹ ^ 2)) measure)
    {numerator denominator : ℝ} (numeratorNonnegative : 0 ≤ numerator) (denominatorPositive : 0 < denominator)
    (commonNumerator : ∀ edge, (∫ outcome,
      max (first (edgeInputs edge outcome) - second (edgeInputs edge outcome)) 0 *
        max 1 ((second (edgeInputs edge outcome))⁻¹ ^ 2) ∂measure) = numerator)
    (commonDenominator : ∀ edge, (∫ outcome,
      min (second (edgeInputs edge outcome)) (second (edgeInputs edge outcome))⁻¹ ∂measure) = denominator) :
    (∫ outcome, max (network.effectiveResistance (fun edge => first (edgeInputs edge outcome)) -
      network.effectiveResistance (fun edge => second (edgeInputs edge outcome))) 0 ∂measure) ≤
      (numerator / denominator) *
        ∫ outcome, network.effectiveResistance (fun edge => second (edgeInputs edge outcome)) ∂measure := by
  let optimalCurrent (outcome : Outcome) := network.minimizingCurrent connected
    (fun edge => second (edgeInputs edge outcome)) (fun edge => secondPositive _)
  let referenceResponse (changed : Edge) (configuration : Edge → State) :=
    network.referenceCurrent connected (fun edge => second (configuration edge)) (fun edge => secondPositive _) changed
  have resistanceInputMeasurable (input : State → ℝ) (inputMeasurable : Measurable input) :
      Measurable (fun outcome edge => input (edgeInputs edge outcome)) :=
    measurable_pi_lambda _ (fun edge => inputMeasurable.comp (measurableEdgeInputs edge))
  have currentMeasurable (changed : Edge) : Measurable (fun outcome => optimalCurrent outcome changed) :=
    (measurable_pi_apply changed).comp (network.minimizingCurrent_measurable connected
      (fun outcome edge => second (edgeInputs edge outcome))
      (resistanceInputMeasurable second secondMeasurable) (fun outcome edge => secondPositive _))
  have referenceMeasurable (changed : Edge) : Measurable (referenceResponse changed) :=
    network.state_referenceCurrent_measurable connected second secondMeasurable secondPositive changed
  have referenceOnOutcomesMeasurable (changed : Edge) :
      Measurable (fun outcome => referenceResponse changed (fun edge => edgeInputs edge outcome)) :=
    (referenceMeasurable changed).comp (measurable_pi_lambda _ measurableEdgeInputs)
  have currentSquareBound (outcome : Outcome) (changed : Edge) : optimalCurrent outcome changed ^ 2 ≤ 1 :=
    network.minimizingCurrent_square_le_one connected _ _ changed
  have referenceSquareBound (configuration : Edge → State) (changed : Edge) :
      referenceResponse changed configuration ^ 2 ≤ 1 :=
    network.referenceCurrent_square_le_one connected _ _ changed
  have referenceInvariant (changed : Edge) (configuration : Edge → State) (value : State) :
      referenceResponse changed (Function.update configuration changed value) ^ 2 =
        referenceResponse changed configuration ^ 2 := by
    have inputUpdateIdentity : (fun edge => second (Function.update configuration changed value edge)) =
        Function.update (fun edge => second (configuration edge)) changed (second value) := by
      funext edge
      by_cases same : edge = changed
      · subst edge
        simp
      · simp [Function.update_of_ne same]
    simp only [referenceResponse, referenceCurrent, inputUpdateIdentity, Function.update_idem]
  have numeratorMeasurable : Measurable (fun value : State =>
      max (first value - second value) 0 * max 1 ((second value)⁻¹ ^ 2)) :=
    ((firstMeasurable.sub secondMeasurable).max measurable_const).mul
      (measurable_const.max (secondMeasurable.inv.pow_const 2))
  have denominatorMeasurable : Measurable (fun value : State => min (second value) (second value)⁻¹) :=
    secondMeasurable.min secondMeasurable.inv
  have denominatorIntegrable (changed : Edge) : Integrable
      (fun outcome => min (second (edgeInputs changed outcome)) (second (edgeInputs changed outcome))⁻¹) measure := by
    apply (secondIntegrable changed).mono'
      (denominatorMeasurable.comp (measurableEdgeInputs changed)).aestronglyMeasurable
    filter_upwards [] with outcome
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (secondPositive _).le (inv_nonneg.mpr (secondPositive _).le))]
    exact min_le_left _ _
  have differenceIntegrable (changed : Edge) : Integrable (fun outcome =>
      max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0) measure := by
    convert ((firstIntegrable changed).sub (secondIntegrable changed)).sup
      (integrable_const (0 : ℝ)) using 1
    ext outcome
    rfl
  have differenceContributionIntegrable (changed : Edge) : Integrable (fun outcome =>
      max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0 *
        optimalCurrent outcome changed ^ 2) measure :=
    integral_mul_bounded_square_integrable measure _ _ (differenceIntegrable changed)
      (currentMeasurable changed) (fun outcome => currentSquareBound outcome changed)
  have energyContributionIntegrable (changed : Edge) : Integrable (fun outcome =>
      second (edgeInputs changed outcome) * optimalCurrent outcome changed ^ 2) measure :=
    integral_mul_bounded_square_integrable measure _ _ (secondIntegrable changed)
      (currentMeasurable changed) (fun outcome => currentSquareBound outcome changed)
  have upperBound (changed : Edge) : (∫ outcome,
      max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0 *
        optimalCurrent outcome changed ^ 2 ∂measure) ≤
      numerator * ∫ outcome, referenceResponse changed (fun edge => edgeInputs edge outcome) ^ 2 ∂measure := by
    have bound := integral_mono (differenceContributionIntegrable changed)
      (integral_mul_bounded_square_integrable measure _ _ (numeratorIntegrable changed)
        (referenceOnOutcomesMeasurable changed) (fun outcome => referenceSquareBound _ changed))
      (fun outcome => network.reference_current_difference_upper_bound connected
        (fun edge => first (edgeInputs edge outcome)) (fun edge => second (edgeInputs edge outcome))
        (fun edge => secondPositive _) changed)
    have factorisation := IGSIII34.Probability.integral_coordinate_factorisation measure edgeInputs
      independent measurableEdgeInputs changed base _ numeratorMeasurable _
      ((referenceMeasurable changed).pow_const 2) (referenceInvariant changed)
    rw [commonNumerator changed] at factorisation
    exact bound.trans_eq factorisation
  have lowerBound (changed : Edge) :
      denominator * (∫ outcome, referenceResponse changed (fun edge => edgeInputs edge outcome) ^ 2 ∂measure) ≤
      ∫ outcome, second (edgeInputs changed outcome) * optimalCurrent outcome changed ^ 2 ∂measure := by
    have bound := integral_mono
      (integral_mul_bounded_square_integrable measure _ _ (denominatorIntegrable changed)
        (referenceOnOutcomesMeasurable changed) (fun outcome => referenceSquareBound _ changed))
      (energyContributionIntegrable changed)
      (fun outcome => network.reference_current_weighted_lower_bound connected
        (fun edge => second (edgeInputs edge outcome)) (fun edge => secondPositive _) changed)
    have factorisation := IGSIII34.Probability.integral_coordinate_factorisation measure edgeInputs
      independent measurableEdgeInputs changed base _ denominatorMeasurable _
      ((referenceMeasurable changed).pow_const 2) (referenceInvariant changed)
    rw [commonDenominator changed] at factorisation
    exact factorisation.symm.trans_le bound
  have edgeComparison (changed : Edge) :
      (∫ outcome, max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0 *
        optimalCurrent outcome changed ^ 2 ∂measure) ≤
      (numerator / denominator) * ∫ outcome,
        second (edgeInputs changed outcome) * optimalCurrent outcome changed ^ 2 ∂measure := by
    apply (upperBound changed).trans
    have dividedBound : (∫ outcome, referenceResponse changed (fun edge => edgeInputs edge outcome) ^ 2 ∂measure) ≤
        (∫ outcome, second (edgeInputs changed outcome) * optimalCurrent outcome changed ^ 2 ∂measure) / denominator := by
      apply (le_div_iff₀ denominatorPositive).mpr
      simpa only [mul_comm] using lowerBound changed
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_left dividedBound numeratorNonnegative
  have firstOutputIntegrable := network.effectiveResistance_integrable measure connected
    (fun outcome edge => first (edgeInputs edge outcome))
    (resistanceInputMeasurable first firstMeasurable) (fun outcome edge => firstPositive _) firstIntegrable
  have secondOutputIntegrable := network.effectiveResistance_integrable measure connected
    (fun outcome edge => second (edgeInputs edge outcome))
    (resistanceInputMeasurable second secondMeasurable) (fun outcome edge => secondPositive _) secondIntegrable
  have outputDifferenceIntegrable : Integrable (fun outcome =>
      max (network.effectiveResistance (fun edge => first (edgeInputs edge outcome)) -
        network.effectiveResistance (fun edge => second (edgeInputs edge outcome))) 0) measure := by
    convert (firstOutputIntegrable.sub secondOutputIntegrable).sup (integrable_const (0 : ℝ)) using 1
    ext outcome
    rfl
  have energyIdentity (outcome : Outcome) :
      (∑ edge, second (edgeInputs edge outcome) * optimalCurrent outcome edge ^ 2) =
        network.effectiveResistance (fun edge => second (edgeInputs edge outcome)) :=
    network.minimizingCurrent_energy connected _ _
  calc
    _ ≤ ∫ outcome, ∑ changed, max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0 *
        optimalCurrent outcome changed ^ 2 ∂measure :=
      integral_mono outputDifferenceIntegrable
        (integrable_finsetSum Finset.univ (fun changed _ => differenceContributionIntegrable changed))
        (fun outcome => network.effectiveResistance_positive_difference_le_trial_sum
          (fun edge => firstPositive _) (network.minimizingCurrent_unitFlow connected _ _)
          (network.minimizingCurrent_energy connected _ _))
    _ = ∑ changed, ∫ outcome,
        max (first (edgeInputs changed outcome) - second (edgeInputs changed outcome)) 0 *
          optimalCurrent outcome changed ^ 2 ∂measure :=
      integral_finsetSum Finset.univ (fun changed _ => differenceContributionIntegrable changed)
    _ ≤ ∑ changed, (numerator / denominator) * ∫ outcome,
        second (edgeInputs changed outcome) * optimalCurrent outcome changed ^ 2 ∂measure :=
      Finset.sum_le_sum (fun changed _ => edgeComparison changed)
    _ = _ := by
      rw [← Finset.mul_sum, ← integral_finsetSum Finset.univ (fun changed _ => energyContributionIntegrable changed)]
      simp only [energyIdentity]

end
end IGSIII34.Resistance.FiniteNetwork
