import IGSIII34.Spectral.ActualMassContinuationCompletion
import IGSIII34.Spectral.AnnealedLiveComponentCountCompletion
import IGSIII34.Percolation.ElectricalPrefix
import Mathlib.Probability.Independence.Integration

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

theorem retainedComponentStateFrom_congr_prefix_completion
    (rule : Rule) (first second : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (word : List (Fin rule.edges × Bool))
    (agree : ∀ address opened, address.length < ancestor.length + word.length →
      first (address, opened) = second (address, opened)) :
    retainedComponentStateFrom rule first ancestor parent word =
      retainedComponentStateFrom rule second ancestor parent word := by
  induction word generalizing ancestor parent with
  | nil => rfl
  | cons choice tail inductionHypothesis =>
    have rootEquality := agree ancestor parent.massOpened (by simp only [List.length_cons]; omega)
    simp only [retainedComponentStateFrom, rootEquality]
    apply inductionHypothesis
    intro address opened length
    apply agree
    simp only [List.length_append, List.length_singleton] at length
    simp only [List.length_cons]
    omega

theorem retainedComponentState_prefix_factor_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (word : List (Fin rule.edges × Bool)) :
    retainedComponentState rule
      (innovationPrefixFill rule word.length (fun coordinate => marks coordinate.val)) word =
        retainedComponentState rule marks word := by
  apply retainedComponentStateFrom_congr_prefix_completion
  intro address opened length
  simp only [List.length_nil, zero_add] at length
  simp only [innovationPrefixFill, dif_pos length]

/-- An arbitrary actual finite-prefix selector sees the correct joint
descendant mass field. Its expectation equals the selected deterministic
mean, and vanishes on inactive selections. -/
theorem prefix_selected_mass_integral_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (address : List (Fin rule.edges))
    (selector : ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < address.length} →
      Configuration rule.edges) → OrientedState)
    (selectorMeasurable : Measurable selector) :
    Integrable (fun marks => continuation.mass
      (selector (fun coordinate => marks coordinate.val)) (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
    (∫ marks, continuation.mass (selector (fun coordinate => marks coordinate.val))
      (innovationTreeShift rule address marks) ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
        ∫ marks, (∫ input, continuation.mass (selector (fun coordinate => marks coordinate.val)) input
          ∂independentInnovationLaw rule p positive belowOne fixedPoint)
            ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  classical
  let history := fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
      (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < address.length}) =>
    marks coordinate.val
  have historyMeasurable : Measurable history := measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)
  let choice := fun marks => selector (history marks)
  have choiceMeasurable : Measurable choice := selectorMeasurable.comp historyMeasurable
  let indicator := fun parent marks => if choice marks = parent then (1 : ℝ) else 0
  have indicatorMeasurable (parent : OrientedState) : Measurable (indicator parent) :=
    Measurable.ite (measurableSet_eq_fun choiceMeasurable measurable_const) measurable_const measurable_const
  have indicatorIntegrable (parent : OrientedState) : Integrable (indicator parent)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply (integrable_const (1 : ℝ)).mono' (indicatorMeasurable parent).aestronglyMeasurable
    exact Eventually.of_forall (fun marks => by dsimp only [indicator]; split_ifs <;> norm_num)
  have shiftedIntegrable (parent : OrientedState) : Integrable
      (fun marks => continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).integrable_comp
      (continuation.measurable parent).aestronglyMeasurable |>.mpr (continuation.integrable parent)
  have shiftedMean (parent : OrientedState) :
      (∫ marks, continuation.mass parent (innovationTreeShift rule address marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
      ∫ marks, continuation.mass parent marks ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
    have transport := integral_map_of_stronglyMeasurable
      (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (innovationTreeShift_measurable rule address) (continuation.measurable parent).stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at transport
    exact transport.symm
  have independent (parent : OrientedState) : IndepFun (indicator parent)
      (fun marks => continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have vector := actual_mass_continuation_prefix_independent_completion
      rule p positive belowOne fixedPoint continuation address
    exact vector.comp
      (Measurable.ite (measurableSet_eq_fun selectorMeasurable measurable_const) measurable_const measurable_const)
      (measurable_pi_apply parent)
  have productIntegrable (parent : OrientedState) : Integrable
      (fun marks => indicator parent marks * continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (independent parent).integrable_mul (indicatorIntegrable parent) (shiftedIntegrable parent)
  have partition (marks) : continuation.mass (choice marks) (innovationTreeShift rule address marks) =
      ∑ parent : OrientedState, indicator parent marks * continuation.mass parent (innovationTreeShift rule address marks) := by
    symm
    rw [Finset.sum_eq_single (choice marks)]
    · simp only [indicator, if_pos rfl, one_mul]
    · intro parent _ distinct
      simp only [indicator, if_neg (Ne.symm distinct), zero_mul]
    · simp
  have meanPartition (marks) :
      (∫ input, continuation.mass (choice marks) input ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
      ∑ parent : OrientedState, indicator parent marks *
        (∫ input, continuation.mass parent input ∂independentInnovationLaw rule p positive belowOne fixedPoint) := by
    symm
    rw [Finset.sum_eq_single (choice marks)]
    · simp only [indicator, if_pos rfl, one_mul]
    · intro parent _ distinct
      simp only [indicator, if_neg (Ne.symm distinct), zero_mul]
    · simp
  refine ⟨?_, ?_⟩
  · exact ((integrable_finsetSum _ (fun parent _ => productIntegrable parent)).congr
      (Eventually.of_forall (fun marks => (partition marks).symm)))
  · change (∫ marks, continuation.mass (choice marks) (innovationTreeShift rule address marks) ∂_) =
      ∫ marks, (∫ input, continuation.mass (choice marks) input ∂_) ∂_
    simp_rw [partition, meanPartition]
    rw [integral_finsetSum _ (fun parent _ => productIntegrable parent),
      integral_finsetSum _ (fun parent _ => (indicatorIntegrable parent).mul_const _)]
    apply Finset.sum_congr rfl
    intro parent _
    rw [(independent parent).integral_fun_mul_eq_mul_integral
      (indicatorMeasurable parent).aestronglyMeasurable
      ((continuation.measurable parent).comp (innovationTreeShift_measurable rule address)).aestronglyMeasurable,
      shiftedMean, integral_mul_const]

end
end IGSIII34.Spectral
