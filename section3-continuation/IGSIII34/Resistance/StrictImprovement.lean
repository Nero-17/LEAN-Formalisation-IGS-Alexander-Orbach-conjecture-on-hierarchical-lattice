import IGSIII34.Resistance.FlowPaths
import Mathlib.Tactic.FieldSimp

/-!
# Strict electrical improvement from an alternative unit flow

This is the quadratic perturbation behind the all-open argument in Section 4.
The result concerns genuine Kirchhoff flows. The separate combinatorial task
is to extract the required alternative path from each classical rule's mincut.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork

noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def crossEnergy (resistance first second : Edge → ℝ) : ℝ :=
  ∑ edge, resistance edge * first edge * second edge

theorem energy_perturbation (resistance current perturbation : Edge → ℝ) (scalar : ℝ) :
    energy resistance (fun edge => current edge + scalar * perturbation edge) =
      energy resistance current + 2 * scalar * crossEnergy resistance current perturbation +
        scalar ^ 2 * energy resistance perturbation := by
  simp only [energy, crossEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem resistance_strictly_below_trial_of_descent
    (network : FiniteNetwork Vertex Edge) {resistance current perturbation : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (zeroDivergence : ∀ vertex, network.divergence perturbation vertex = 0)
    (descent : crossEnergy resistance current perturbation < 0)
    (directionEnergyPositive : 0 < energy resistance perturbation) :
    network.effectiveResistance resistance < energy resistance current := by
  have admissible := network.unitFlow_add_zero_divergence unitFlow zeroDivergence
    (-crossEnergy resistance current perturbation / energy resistance perturbation)
  apply lt_of_le_of_lt (network.effectiveResistance_le_energy nonnegative admissible)
  rw [energy_perturbation]
  have strictDecrease :
      energy resistance current +
          2 * (-crossEnergy resistance current perturbation / energy resistance perturbation) *
            crossEnergy resistance current perturbation +
          (-crossEnergy resistance current perturbation / energy resistance perturbation) ^ 2 *
            energy resistance perturbation =
        energy resistance current -
          crossEnergy resistance current perturbation ^ 2 / energy resistance perturbation := by
    field_simp
    <;> ring
  rw [strictDecrease]
  have positiveDecrease : 0 < crossEnergy resistance current perturbation ^ 2 /
      energy resistance perturbation :=
    div_pos (sq_pos_of_ne_zero (ne_of_lt descent)) directionEnergyPositive
  linarith

end
end IGSIII34.Resistance.FiniteNetwork
