import IGSIII34.Resistance.OneEdge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def minimizingCurrent (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) : Edge → ℝ :=
  Classical.choose (network.exists_minimizing_unitFlow_of_connected connected positive)

theorem minimizingCurrent_unitFlow (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    network.minimizingCurrent connected resistance positive ∈ network.unitFlows :=
  (Classical.choose_spec (network.exists_minimizing_unitFlow_of_connected connected positive)).1

theorem minimizingCurrent_energy (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    energy resistance (network.minimizingCurrent connected resistance positive) =
      network.effectiveResistance resistance :=
  (Classical.choose_spec (network.exists_minimizing_unitFlow_of_connected connected positive)).2

theorem effectiveResistance_positive_difference_le_trial_sum
    (network : FiniteNetwork Vertex Edge) {first second current : Edge → ℝ}
    (firstPositive : ∀ edge, 0 < first edge)
    (unitFlow : current ∈ network.unitFlows)
    (minimal : energy second current = network.effectiveResistance second) :
    max (network.effectiveResistance first - network.effectiveResistance second) 0 ≤
      ∑ edge, max (first edge - second edge) 0 * current edge ^ 2 := by
  have differenceIdentity : energy first current - energy second current =
      ∑ edge, (first edge - second edge) * current edge ^ 2 := by
    simp only [energy, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  have trial := network.effectiveResistance_le_energy (fun edge => (firstPositive edge).le) unitFlow
  rw [max_le_iff]
  constructor
  · calc
      _ ≤ energy first current - energy second current := by rw [minimal]; linarith
      _ = _ := differenceIdentity
      _ ≤ _ := Finset.sum_le_sum (fun edge _ =>
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · exact Finset.sum_nonneg (fun edge _ => mul_nonneg (le_max_right _ _) (sq_nonneg _))

def referenceCurrent (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge) : ℝ :=
  network.minimizingCurrent connected (Function.update resistance changed 1)
    (fun edge => by
      by_cases same : edge = changed
      · subst edge
        simp only [Function.update_self, zero_lt_one]
      · simpa only [Function.update_of_ne same] using positive edge) changed

theorem minimizingCurrent_sq_bounds_by_reference (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge) :
    min 1 ((resistance changed)⁻¹ ^ 2) * network.referenceCurrent connected resistance positive changed ^ 2 ≤
      network.minimizingCurrent connected resistance positive changed ^ 2 ∧
    network.minimizingCurrent connected resistance positive changed ^ 2 ≤
      max 1 ((resistance changed)⁻¹ ^ 2) * network.referenceCurrent connected resistance positive changed ^ 2 := by
  have referencePositive (edge : Edge) : 0 < Function.update resistance changed 1 edge := by
    by_cases same : edge = changed
    · subst edge
      simp
    · simpa only [Function.update_of_ne same] using positive edge
  have updateIdentity : Function.update (Function.update resistance changed 1) changed
      (resistance changed) = resistance := by
    rw [Function.update_idem, Function.update_eq_self]
  have bound := network.single_edge_minimizing_current_square_bounds changed referencePositive
    (Function.update_self changed 1 resistance) (positive changed)
    (network.minimizingCurrent_unitFlow connected _ referencePositive)
    (network.minimizingCurrent_unitFlow connected resistance positive)
    (network.minimizingCurrent_energy connected _ referencePositive)
    (by rw [updateIdentity]; exact network.minimizingCurrent_energy connected resistance positive)
  exact bound

theorem positive_mul_min_inverse_sq {value : ℝ} (positive : 0 < value) :
    value * min 1 (value⁻¹ ^ 2) = min value value⁻¹ := by
  have inverseNonnegative := inv_nonneg.mpr positive.le
  have inverseIdentity : value * value⁻¹ ^ 2 = value⁻¹ := by field_simp
  by_cases small : value ≤ 1
  · have inverseLarge : 1 ≤ value⁻¹ := (one_le_inv₀ positive).mpr small
    rw [min_eq_left (by nlinarith : 1 ≤ value⁻¹ ^ 2),
      min_eq_left (small.trans inverseLarge), mul_one]
  · have large : 1 ≤ value := le_of_lt (lt_of_not_ge small)
    have inverseSmall : value⁻¹ ≤ 1 := (inv_le_one₀ positive).mpr large
    rw [min_eq_right (by nlinarith : value⁻¹ ^ 2 ≤ 1),
      min_eq_right (inverseSmall.trans large), inverseIdentity]

theorem reference_current_weighted_lower_bound (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge) :
    min (resistance changed) (resistance changed)⁻¹ *
      network.referenceCurrent connected resistance positive changed ^ 2 ≤
    resistance changed * network.minimizingCurrent connected resistance positive changed ^ 2 := by
  have bound := mul_le_mul_of_nonneg_left
    (network.minimizingCurrent_sq_bounds_by_reference connected resistance positive changed).1
    (positive changed).le
  simpa only [← mul_assoc, positive_mul_min_inverse_sq (positive changed)] using bound

theorem reference_current_difference_upper_bound (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (first second : Edge → ℝ) (secondPositive : ∀ edge, 0 < second edge) (changed : Edge) :
    max (first changed - second changed) 0 *
      network.minimizingCurrent connected second secondPositive changed ^ 2 ≤
    (max (first changed - second changed) 0 * max 1 ((second changed)⁻¹ ^ 2)) *
      network.referenceCurrent connected second secondPositive changed ^ 2 := by
  have bound := mul_le_mul_of_nonneg_left
    (network.minimizingCurrent_sq_bounds_by_reference connected second secondPositive changed).2
    (le_max_right (first changed - second changed) 0)
  simpa only [mul_assoc] using bound

theorem referenceCurrent_update_invariant (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (changed : Edge)
    (value : ℝ) (updatedPositive : ∀ edge, 0 < Function.update resistance changed value edge) :
    network.referenceCurrent connected (Function.update resistance changed value) updatedPositive changed =
      network.referenceCurrent connected resistance positive changed := by
  simp only [referenceCurrent, Function.update_idem]

end
end IGSIII34.Resistance.FiniteNetwork
