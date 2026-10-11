import IGSIII34.Spectral.MaskedMassExpectationCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.Percolation MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

local instance : MeasurableSpace OrientedState := ⊤
local instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

theorem prefix_selected_mass_integral_live_bound_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (address : List (Fin rule.edges))
    (selector : ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < address.length} →
      Configuration rule.edges) → OrientedState)
    (selectorMeasurable : Measurable selector) :
    (∫ marks, continuation.mass (selector (fun coordinate => marks coordinate.val))
      (innovationTreeShift rule address marks) ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
        continuation.meanBound * ∫ marks,
          (if selector (fun coordinate => marks coordinate.val) ≠ .inactive then (1 : ℝ) else 0)
            ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  classical
  have equality := (prefix_selected_mass_integral_completion20261011 rule p positive belowOne
    fixedPoint continuation address selector selectorMeasurable).2
  rw [equality]
  let choice := fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) =>
    selector (fun coordinate => marks coordinate.val)
  have choiceMeasurable : Measurable choice := selectorMeasurable.comp
    (measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val))
  let means := fun parent => ∫ input, continuation.mass parent input
    ∂independentInnovationLaw rule p positive belowOne fixedPoint
  have nonnegative (parent : OrientedState) : 0 ≤ means parent := integral_nonneg (continuation.nonnegative parent)
  have inactiveZero : means .inactive = 0 := by
    rw [show means .inactive = ∫ input, continuation.mass .inactive input
      ∂independentInnovationLaw rule p positive belowOne fixedPoint from rfl,
      integral_congr_ae continuation.inactive, integral_zero]
  have meanMeasurable : Measurable (fun marks => means (choice marks)) :=
    (measurable_of_countable means).comp choiceMeasurable
  have meanIntegrable : Integrable (fun marks => means (choice marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply (integrable_const continuation.meanBound).mono' meanMeasurable.aestronglyMeasurable
    apply Eventually.of_forall
    intro marks
    rw [Real.norm_eq_abs, abs_of_nonneg (nonnegative _)]
    exact continuation.means _
  let live := fun marks => if choice marks ≠ .inactive then (1 : ℝ) else 0
  have liveMeasurable : Measurable live := Measurable.ite
    (measurableSet_eq_fun choiceMeasurable measurable_const).compl measurable_const measurable_const
  have liveIntegrable : Integrable live (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply (integrable_const (1 : ℝ)).mono' liveMeasurable.aestronglyMeasurable
    exact Eventually.of_forall (fun marks => by dsimp only [live]; split_ifs <;> norm_num)
  change (∫ marks, means (choice marks) ∂_) ≤ continuation.meanBound * ∫ marks, live marks ∂_
  rw [← integral_const_mul]
  apply integral_mono meanIntegrable (liveIntegrable.const_mul continuation.meanBound)
  intro marks
  dsimp only [live]
  split_ifs with liveState
  · simpa only [mul_one] using continuation.means (choice marks)
  · have state : choice marks = .inactive := not_ne_iff.mp liveState
    rw [state, inactiveZero, mul_zero]

/-- Expected mass of one actual retained component is bounded by its live
probability. The selector uses the same original innovations as the mass
continuation and therefore does not replace a B socket by independent sides. -/
theorem actual_retained_component_mass_integral_bound_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (word : List (Fin rule.edges × Bool)) :
    Integrable (fun marks => continuation.mass (retainedComponentState rule marks word)
      (innovationTreeShift rule (componentEdgeAddress word) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
    (∫ marks, continuation.mass (retainedComponentState rule marks word)
      (innovationTreeShift rule (componentEdgeAddress word) marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      continuation.meanBound * ∫ marks,
        (if retainedComponentState rule marks word ≠ .inactive then (1 : ℝ) else 0)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have length : (componentEdgeAddress word).length = word.length := by
    simp only [componentEdgeAddress, List.length_map]
  let selector := fun input : ({coordinate : List (Fin rule.edges) × Bool //
      coordinate.1.length < (componentEdgeAddress word).length} → Configuration rule.edges) =>
    retainedComponentState rule (innovationPrefixFill rule (componentEdgeAddress word).length input) word
  have selectorMeasurable : Measurable selector :=
    (retainedComponentStateFrom_measurable_completion20261011 rule [] word
      (fun _ => .connected) measurable_const).comp
        (innovationPrefixFill_measurable rule (componentEdgeAddress word).length)
  have prefixEquality (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
      selector (fun coordinate => marks coordinate.val) = retainedComponentState rule marks word := by
    dsimp only [selector]
    apply retainedComponentStateFrom_congr_prefix_completion20261011
    intro address opened shorter
    simp only [List.length_nil, zero_add] at shorter
    simp only [innovationPrefixFill, dif_pos (show address.length < (componentEdgeAddress word).length by rw [length]; exact shorter)]
  have integrable := (prefix_selected_mass_integral_completion20261011 rule p positive belowOne
    fixedPoint continuation (componentEdgeAddress word) selector selectorMeasurable).1
  have bound := prefix_selected_mass_integral_live_bound_completion20261011 rule p positive belowOne
    fixedPoint continuation (componentEdgeAddress word) selector selectorMeasurable
  simpa only [prefixEquality] using And.intro integrable bound

end
end IGSIII34.Spectral
