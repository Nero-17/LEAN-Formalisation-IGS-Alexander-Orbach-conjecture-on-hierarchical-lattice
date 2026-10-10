import IGSIII34.Resistance.RandomComparison
import IGSIII34.Resistance.CurrentBound

set_option autoImplicit false
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem energy_update (resistance current : Edge → ℝ) (changed : Edge) (value : ℝ) :
    energy (Function.update resistance changed value) current =
      energy resistance current + (value - resistance changed) * current changed ^ 2 := by
  classical
  simp only [energy]
  have summands (edge : Edge) : Function.update resistance changed value edge * current edge ^ 2 =
      resistance edge * current edge ^ 2 +
        if edge = changed then (value - resistance changed) * current changed ^ 2 else 0 := by
    by_cases same : edge = changed
    · subst edge
      simp only [Function.update_self, ↓reduceIte]
      ring
    · simp only [Function.update_of_ne same, same, ↓reduceIte, add_zero]
  simp only [summands, Finset.sum_add_distrib]
  simp

theorem resistance_resampling_positivePart_sq_le (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (changed : Edge) (replacement : ℝ) (replacementNonnegative : 0 ≤ replacement) :
    (max (network.effectiveResistance (Function.update resistance changed replacement) -
      network.effectiveResistance resistance) 0) ^ 2 ≤
        replacement ^ 2 * network.minimizingCurrent connected resistance positive changed ^ 4 := by
  have trial := network.effectiveResistance_le_energy
    (resistance := Function.update resistance changed replacement)
    (fun edge => by
      by_cases same : edge = changed
      · subst edge; simpa only [Function.update_self] using replacementNonnegative
      · simpa only [Function.update_of_ne same] using (positive edge).le)
    (network.minimizingCurrent_unitFlow connected resistance positive)
  rw [energy_update, network.minimizingCurrent_energy connected resistance positive] at trial
  have upper : max (network.effectiveResistance (Function.update resistance changed replacement) -
      network.effectiveResistance resistance) 0 ≤
        replacement * network.minimizingCurrent connected resistance positive changed ^ 2 := by
    apply max_le
    · nlinarith [mul_nonneg (positive changed).le
        (sq_nonneg (network.minimizingCurrent connected resistance positive changed))]
    · exact mul_nonneg replacementNonnegative (sq_nonneg _)
  have squared := pow_le_pow_left₀ (le_max_right _ _) upper 2
  calc
    _ ≤ (replacement * network.minimizingCurrent connected resistance positive changed ^ 2) ^ 2 := squared
    _ = _ := by ring

theorem fourth_current_sum_le_resistance_inverse_bound (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (inverseBound : ℝ) (inverseBoundHolds : ∀ edge, (resistance edge)⁻¹ ≤ inverseBound) :
    (∑ edge, network.minimizingCurrent connected resistance positive edge ^ 4) ≤
      inverseBound * network.effectiveResistance resistance := by
  have currentBound := network.minimizing_current_abs_le_one positive
    (network.minimizingCurrent_unitFlow connected resistance positive)
    (network.minimizingCurrent_energy connected resistance positive)
  calc
    _ ≤ ∑ edge, inverseBound * (resistance edge *
        network.minimizingCurrent connected resistance positive edge ^ 2) := by
      apply Finset.sum_le_sum
      intro edge _
      have squareBound : network.minimizingCurrent connected resistance positive edge ^ 2 ≤ 1 := by
        nlinarith [sq_abs (network.minimizingCurrent connected resistance positive edge),
          abs_nonneg (network.minimizingCurrent connected resistance positive edge), currentBound edge]
      have weightedOne : 1 ≤ resistance edge * inverseBound := by
        have multiplied := mul_le_mul_of_nonneg_left (inverseBoundHolds edge) (positive edge).le
        simpa only [mul_inv_cancel₀ (positive edge).ne'] using multiplied
      have squareNonnegative := sq_nonneg (network.minimizingCurrent connected resistance positive edge)
      have comparison := mul_le_mul_of_nonneg_right weightedOne squareNonnegative
      nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 -
        network.minimizingCurrent connected resistance positive edge ^ 2 ≥ 0 from by linarith)) squareNonnegative]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact network.minimizingCurrent_energy connected resistance positive

end
end IGSIII34.Resistance.FiniteNetwork
