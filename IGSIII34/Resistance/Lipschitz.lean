import IGSIII34.Resistance.CurrentBound

/-! The electrical Lipschitz estimate, derived from actual optimal currents. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem trial_energy_difference_le_sum_abs (first second current : Edge → ℝ)
    (currentBound : ∀ edge, |current edge| ≤ 1) :
    energy second current ≤ energy first current + ∑ edge, |second edge - first edge| := by
  have identity : energy second current = energy first current +
      ∑ edge, (second edge - first edge) * current edge ^ 2 := by
    simp only [energy, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  rw [identity]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro edge _
  have squareBound : current edge ^ 2 ≤ 1 := by
    have bound := currentBound edge
    nlinarith [abs_nonneg (current edge), sq_abs (current edge)]
  calc
    (second edge - first edge) * current edge ^ 2 ≤
        |second edge - first edge| * current edge ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    _ ≤ |second edge - first edge| := by
      simpa using mul_le_mul_of_nonneg_left squareBound (abs_nonneg (second edge - first edge))

theorem effectiveResistance_le_add_sum_abs (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {first second : Edge → ℝ}
    (firstPositive : ∀ edge, 0 < first edge)
    (secondPositive : ∀ edge, 0 < second edge) :
    network.effectiveResistance second ≤ network.effectiveResistance first +
      ∑ edge, |second edge - first edge| := by
  obtain ⟨current, unitFlow, minimal⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected firstPositive
  calc
    network.effectiveResistance second ≤ energy second current :=
      network.effectiveResistance_le_energy (fun edge => (secondPositive edge).le) unitFlow
    _ ≤ energy first current + ∑ edge, |second edge - first edge| :=
      trial_energy_difference_le_sum_abs first second current
        (network.minimizing_current_abs_le_one firstPositive unitFlow minimal)
    _ = _ := by rw [minimal]

theorem effectiveResistance_abs_sub_le_sum_abs (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {first second : Edge → ℝ}
    (firstPositive : ∀ edge, 0 < first edge)
    (secondPositive : ∀ edge, 0 < second edge) :
    |network.effectiveResistance first - network.effectiveResistance second| ≤
      ∑ edge, |first edge - second edge| := by
  rw [abs_sub_le_iff]
  constructor
  · have bound := network.effectiveResistance_le_add_sum_abs connected secondPositive firstPositive
    linarith
  · have bound := network.effectiveResistance_le_add_sum_abs connected firstPositive secondPositive
    simp_rw [abs_sub_comm (second _) (first _)] at bound
    linarith

end
end IGSIII34.Resistance.FiniteNetwork
