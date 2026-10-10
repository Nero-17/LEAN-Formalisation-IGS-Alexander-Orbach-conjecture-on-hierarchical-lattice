import IGSIII34.Resistance.IntegralJensen
import IGSIII34.Resistance.FiniteComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory

attribute [local irreducible] effectiveResistance

variable {Vertex Edge State : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [MeasurableSpace State]

theorem state_resistance_input_measurable (resistance : State → ℝ) (measurableInput : Measurable resistance) :
    Measurable (fun configuration : Edge → State => fun edge => resistance (configuration edge)) :=
  measurable_pi_lambda _ (fun edge => measurableInput.comp (measurable_pi_apply edge))

theorem state_referenceCurrent_measurable (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : State → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ value, 0 < resistance value) (changed : Edge) :
    Measurable (fun configuration : Edge → State =>
      network.referenceCurrent connected (fun edge => resistance (configuration edge))
        (fun edge => positive _) changed) := by
  have referenceMeasurable : Measurable (fun configuration : Edge → State =>
      Function.update (fun edge => resistance (configuration edge)) changed 1) := by
    apply measurable_pi_lambda
    intro edge
    by_cases same : edge = changed
    · subst edge
      simpa only [Function.update_self] using (measurable_const (a := (1 : ℝ)))
    · simpa only [Function.update_of_ne same, Function.comp_def] using
        measurableInput.comp (measurable_pi_apply edge)
  have referencePositive (configuration : Edge → State) (edge : Edge) :
      0 < Function.update (fun edge => resistance (configuration edge)) changed 1 edge := by
    by_cases same : edge = changed
    · subst edge
      simp
    · simpa only [Function.update_of_ne same] using positive (configuration edge)
  exact (measurable_pi_apply changed).comp
    (network.minimizingCurrent_measurable connected _ referenceMeasurable referencePositive)

theorem minimizingCurrent_square_le_one (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge) :
    network.minimizingCurrent connected resistance positive changed ^ 2 ≤ 1 := by
  have bound := network.minimizing_current_abs_le_one positive
    (network.minimizingCurrent_unitFlow connected resistance positive)
    (network.minimizingCurrent_energy connected resistance positive) changed
  nlinarith [abs_nonneg (network.minimizingCurrent connected resistance positive changed),
    sq_abs (network.minimizingCurrent connected resistance positive changed)]

theorem referenceCurrent_square_le_one (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge) :
    network.referenceCurrent connected resistance positive changed ^ 2 ≤ 1 := by
  unfold referenceCurrent
  exact network.minimizingCurrent_square_le_one connected _ _ changed

theorem integral_mul_bounded_square_integrable {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (scalar current : Outcome → ℝ)
    (scalarIntegrable : Integrable scalar measure) (currentMeasurable : Measurable current)
    (squareBound : ∀ outcome, current outcome ^ 2 ≤ 1) :
    Integrable (fun outcome => scalar outcome * current outcome ^ 2) measure := by
  apply scalarIntegrable.norm.mono'
    (scalarIntegrable.aestronglyMeasurable.mul (currentMeasurable.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with outcome
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs (current outcome ^ 2), abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (squareBound outcome) (norm_nonneg (scalar outcome))

end
end IGSIII34.Resistance.FiniteNetwork
