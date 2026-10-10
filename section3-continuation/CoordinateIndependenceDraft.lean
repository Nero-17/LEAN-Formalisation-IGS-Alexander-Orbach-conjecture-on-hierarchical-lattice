import IGSIII34.Probability.FiniteProduct
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Probability
noncomputable section
open MeasureTheory ProbabilityTheory

variable {Edge State Outcome : Type*} [Fintype Edge] [DecidableEq Edge]
  [MeasurableSpace State] [MeasurableSpace Outcome]

theorem indepFun_coordinate_invariant (measure : Measure Outcome)
    (edgeInputs : Edge → Outcome → State) (independent : iIndepFun edgeInputs measure)
    (measurableVariables : ∀ edge, Measurable (edgeInputs edge)) (changed : Edge) (base : State)
    (response : (Edge → State) → ℝ) (measurableResponse : Measurable response)
    (invariant : ∀ configuration value, response (Function.update configuration changed value) = response configuration) :
    IndepFun (edgeInputs changed) (fun outcome => response (fun edge => edgeInputs edge outcome)) measure := by
  classical
  let fill : ({edge : Edge // edge ∈ (Finset.univ.erase changed : Finset Edge)} → State) → Edge → State :=
    fun rest => insertCoordinate changed base
      (fun edge => rest ⟨edge.val, by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact edge.property⟩)
  have fillMeasurable : Measurable fill := by
    apply measurable_pi_lambda
    intro edge
    by_cases same : edge = changed
    · subst edge
      simpa only [fill, insertCoordinate, ↓reduceDIte] using (measurable_const (a := base))
    · simpa only [fill, insertCoordinate, same, ↓reduceDIte] using
        (measurable_pi_apply (⟨edge, by simp [same]⟩ : (Finset.univ.erase changed : Finset Edge)))
  have responseIdentity :
      (fun outcome => response (fun edge => edgeInputs edge outcome)) =
        (fun outcome => response (fill (fun edge => edgeInputs edge.val outcome))) := by
    funext outcome
    have fillIdentity : fill (fun edge => edgeInputs edge.val outcome) =
        Function.update (fun edge => edgeInputs edge outcome) changed base := by
      funext edge
      by_cases same : edge = changed
      · subst edge
        simp [fill, insertCoordinate]
      · simp [fill, insertCoordinate, Function.update_of_ne same, same]
    rw [fillIdentity, invariant]
  rw [responseIdentity]
  have tupleIndependent := independent.indepFun_finset {changed} (Finset.univ.erase changed)
    (by simp) measurableVariables
  have composed := tupleIndependent.comp
    (measurable_pi_apply (⟨changed, by simp⟩ : ({changed} : Finset Edge)))
    (measurableResponse.comp fillMeasurable)
  exact composed

theorem integral_coordinate_factorisation (measure : Measure Outcome)
    (edgeInputs : Edge → Outcome → State) (independent : iIndepFun edgeInputs measure)
    (measurableVariables : ∀ edge, Measurable (edgeInputs edge)) (changed : Edge) (base : State)
    (localResponse : State → ℝ) (measurableLocalResponse : Measurable localResponse)
    (otherResponse : (Edge → State) → ℝ) (measurableOtherResponse : Measurable otherResponse)
    (invariant : ∀ configuration value,
      otherResponse (Function.update configuration changed value) = otherResponse configuration) :
    (∫ outcome, localResponse (edgeInputs changed outcome) *
      otherResponse (fun edge => edgeInputs edge outcome) ∂measure) =
      (∫ outcome, localResponse (edgeInputs changed outcome) ∂measure) *
        ∫ outcome, otherResponse (fun edge => edgeInputs edge outcome) ∂measure := by
  have responseIndependent := indepFun_coordinate_invariant measure edgeInputs independent
    measurableVariables changed base otherResponse measurableOtherResponse invariant
  exact (responseIndependent.comp measurableLocalResponse measurable_id).integral_fun_mul_eq_mul_integral
    ((measurableLocalResponse.comp (measurableVariables changed)).aestronglyMeasurable)
    ((measurableOtherResponse.comp (measurable_pi_lambda _ measurableVariables)).aestronglyMeasurable)

end
end IGSIII34.Probability

