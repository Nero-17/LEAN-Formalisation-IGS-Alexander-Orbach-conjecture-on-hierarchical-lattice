import IGSIII34.Resistance.IntegralComparison
import Mathlib.Probability.IdentDistrib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory ProbabilityTheory

attribute [local irreducible] effectiveResistance

variable {Vertex Edge State Outcome : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [MeasurableSpace State] [MeasurableSpace Outcome]

/-- The general iid comparison, with integrability stated explicitly. The
two members of each resistance pair may be dependent. -/
theorem iid_resistance_integral_comparison
    (measure : Measure Outcome) [IsProbabilityMeasure measure]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (edgeInputs : Edge → Outcome → State) (independent : iIndepFun edgeInputs measure)
    (measurableEdgeInputs : ∀ edge, Measurable (edgeInputs edge)) (base : State) (reference : Edge)
    (sameLaw : ∀ edge, IdentDistrib (edgeInputs edge) (edgeInputs reference) measure measure)
    (first second : State → ℝ) (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (firstPositive : ∀ value, 0 < first value) (secondPositive : ∀ value, 0 < second value)
    (firstIntegrable : Integrable (fun outcome => first (edgeInputs reference outcome)) measure)
    (secondIntegrable : Integrable (fun outcome => second (edgeInputs reference outcome)) measure)
    (numeratorIntegrable : Integrable (fun outcome =>
      max (first (edgeInputs reference outcome) - second (edgeInputs reference outcome)) 0 *
        max 1 ((second (edgeInputs reference outcome))⁻¹ ^ 2)) measure) :
    (∫ outcome, max (network.effectiveResistance (fun edge => first (edgeInputs edge outcome)) -
      network.effectiveResistance (fun edge => second (edgeInputs edge outcome))) 0 ∂measure) ≤
      ((∫ outcome,
          max (first (edgeInputs reference outcome) - second (edgeInputs reference outcome)) 0 *
            max 1 ((second (edgeInputs reference outcome))⁻¹ ^ 2) ∂measure) /
        (∫ outcome, min (second (edgeInputs reference outcome))
          (second (edgeInputs reference outcome))⁻¹ ∂measure)) *
        ∫ outcome, network.effectiveResistance (fun edge => second (edgeInputs edge outcome)) ∂measure := by
  have numeratorMeasurable : Measurable (fun value : State =>
      max (first value - second value) 0 * max 1 ((second value)⁻¹ ^ 2)) :=
    ((firstMeasurable.sub secondMeasurable).max measurable_const).mul
      (measurable_const.max (secondMeasurable.inv.pow_const 2))
  have denominatorMeasurable : Measurable (fun value : State => min (second value) (second value)⁻¹) :=
    secondMeasurable.min secondMeasurable.inv
  have firstIntegrableEverywhere (edge : Edge) :
      Integrable (fun outcome => first (edgeInputs edge outcome)) measure :=
    ((sameLaw edge).comp firstMeasurable).integrable_iff.mpr firstIntegrable
  have secondIntegrableEverywhere (edge : Edge) :
      Integrable (fun outcome => second (edgeInputs edge outcome)) measure :=
    ((sameLaw edge).comp secondMeasurable).integrable_iff.mpr secondIntegrable
  have numeratorIntegrableEverywhere (edge : Edge) : Integrable (fun outcome =>
      max (first (edgeInputs edge outcome) - second (edgeInputs edge outcome)) 0 *
        max 1 ((second (edgeInputs edge outcome))⁻¹ ^ 2)) measure :=
    ((sameLaw edge).comp numeratorMeasurable).integrable_iff.mpr numeratorIntegrable
  have denominatorIntegrable : Integrable (fun outcome =>
      min (second (edgeInputs reference outcome)) (second (edgeInputs reference outcome))⁻¹) measure := by
    apply secondIntegrable.mono'
      (denominatorMeasurable.comp (measurableEdgeInputs reference)).aestronglyMeasurable
    filter_upwards [] with outcome
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (secondPositive _).le (inv_nonneg.mpr (secondPositive _).le))]
    exact min_le_left _ _
  have denominatorPositive : 0 < ∫ outcome,
      min (second (edgeInputs reference outcome)) (second (edgeInputs reference outcome))⁻¹ ∂measure := by
    apply (integral_pos_iff_support_of_nonneg
      (fun outcome => (le_min (secondPositive _).le (inv_nonneg.mpr (secondPositive _).le)))
      denominatorIntegrable).mpr
    have fullSupport : Function.support (fun outcome =>
        min (second (edgeInputs reference outcome)) (second (edgeInputs reference outcome))⁻¹) = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro outcome
      exact (lt_min (secondPositive _) (inv_pos.mpr (secondPositive _))).ne'
    rw [fullSupport]
    simp
  apply network.independent_pair_resistance_integral_comparison measure connected edgeInputs independent
    measurableEdgeInputs base first second firstMeasurable secondMeasurable firstPositive secondPositive
    firstIntegrableEverywhere secondIntegrableEverywhere numeratorIntegrableEverywhere
    (integral_nonneg (fun outcome => mul_nonneg (le_max_right _ _)
      (zero_le_one.trans (le_max_left _ _)))) denominatorPositive
  · intro edge
    exact ((sameLaw edge).comp numeratorMeasurable).integral_eq
  · intro edge
    exact ((sameLaw edge).comp denominatorMeasurable).integral_eq

end
end IGSIII34.Resistance.FiniteNetwork
