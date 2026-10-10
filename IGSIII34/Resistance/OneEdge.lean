import IGSIII34.Resistance.Orthogonality
import IGSIII34.Resistance.TheveninBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem divergence_sub (network : FiniteNetwork Vertex Edge)
    (first second : Edge → ℝ) (vertex : Vertex) :
    network.divergence (fun edge => first edge - second edge) vertex =
      network.divergence first vertex - network.divergence second vertex := by
  simp only [divergence, sub_mul, Finset.sum_sub_distrib]

theorem unitFlow_sub_zero_divergence (network : FiniteNetwork Vertex Edge)
    {first second : Edge → ℝ} (firstFlow : first ∈ network.unitFlows)
    (secondFlow : second ∈ network.unitFlows) (vertex : Vertex) :
    network.divergence (fun edge => first edge - second edge) vertex = 0 := by
  rw [network.divergence_sub, firstFlow vertex, secondFlow vertex, sub_self]

theorem crossEnergy_update (resistance first second : Edge → ℝ) (changed : Edge) (value : ℝ) :
    crossEnergy (Function.update resistance changed value) first second =
      crossEnergy resistance first second +
        (value - resistance changed) * first changed * second changed := by
  classical
  have pointwise (edge : Edge) :
      Function.update resistance changed value edge * first edge * second edge =
        resistance edge * first edge * second edge +
          if edge = changed then (value - resistance changed) * first changed * second changed else 0 := by
    by_cases same : edge = changed
    · subst edge
      simp only [Function.update_self, ↓reduceIte]
      ring
    · simp only [Function.update_of_ne same, same, ↓reduceIte, add_zero]
  simp only [crossEnergy, pointwise, Finset.sum_add_distrib]
  simp

theorem energy_sub_eq_cross_sub (resistance first second : Edge → ℝ) :
    energy resistance (fun edge => first edge - second edge) =
      crossEnergy resistance first (fun edge => first edge - second edge) -
        crossEnergy resistance second (fun edge => first edge - second edge) := by
  simp only [energy, crossEnergy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem single_edge_minimizing_current_interval
    (network : FiniteNetwork Vertex Edge) {resistance first second : Edge → ℝ}
    (changed : Edge) (resistancePositive : ∀ edge, 0 < resistance edge)
    (referenceValue : resistance changed = 1) {value : ℝ} (valuePositive : 0 < value)
    (firstFlow : first ∈ network.unitFlows) (secondFlow : second ∈ network.unitFlows)
    (firstMinimal : energy resistance first = network.effectiveResistance resistance)
    (secondMinimal : energy (Function.update resistance changed value) second =
      network.effectiveResistance (Function.update resistance changed value)) :
    (second changed - first changed) * (value * second changed - first changed) ≤ 0 := by
  have updatedPositive (edge : Edge) : 0 < Function.update resistance changed value edge := by
    by_cases same : edge = changed
    · subst edge
      simpa only [Function.update_self] using valuePositive
    · simpa only [Function.update_of_ne same] using resistancePositive edge
  have zeroDivergence := network.unitFlow_sub_zero_divergence secondFlow firstFlow
  have firstOrthogonal := network.minimizing_current_orthogonal resistancePositive firstFlow
    firstMinimal zeroDivergence
  have secondOrthogonal := network.minimizing_current_orthogonal updatedPositive secondFlow
    secondMinimal zeroDivergence
  rw [crossEnergy_update, referenceValue] at secondOrthogonal
  have differenceEnergy := energy_sub_eq_cross_sub resistance second first
  rw [firstOrthogonal, sub_zero] at differenceEnergy
  have edgeBound := Finset.single_le_sum (fun edge _ =>
    mul_nonneg (resistancePositive edge).le (sq_nonneg (second edge - first edge)))
    (Finset.mem_univ changed)
  change resistance changed * (second changed - first changed) ^ 2 ≤
    energy resistance (fun edge => second edge - first edge) at edgeBound
  rw [referenceValue, one_mul, differenceEnergy] at edgeBound
  nlinarith

theorem current_interval_square_bounds {value reference current : ℝ}
    (valuePositive : 0 < value)
    (interval : (current - reference) * (value * current - reference) ≤ 0) :
    min 1 (value⁻¹ ^ 2) * reference ^ 2 ≤ current ^ 2 ∧
      current ^ 2 ≤ max 1 (value⁻¹ ^ 2) * reference ^ 2 := by
  have nonnegativeReference {reference current : ℝ} (referenceNonnegative : 0 ≤ reference)
      (interval : (current - reference) * (value * current - reference) ≤ 0) :
      min 1 (value⁻¹ ^ 2) * reference ^ 2 ≤ current ^ 2 ∧
        current ^ 2 ≤ max 1 (value⁻¹ ^ 2) * reference ^ 2 := by
    have between :
        (current ≤ reference ∧ reference / value ≤ current) ∨
          (reference ≤ current ∧ current ≤ reference / value) := by
      rcases mul_nonpos_iff.mp interval with first | second
      · exact Or.inr ⟨by linarith [first.1],
          (le_div_iff₀ valuePositive).mpr (by nlinarith [first.2])⟩
      · exact Or.inl ⟨by linarith [second.1],
          (div_le_iff₀ valuePositive).mpr (by nlinarith [second.2])⟩
    have reciprocalNonnegative : 0 ≤ value⁻¹ := inv_nonneg.mpr valuePositive.le
    have dividedNonnegative : 0 ≤ reference / value := div_nonneg referenceNonnegative valuePositive.le
    by_cases small : value ≤ 1
    · have reciprocalLarge : 1 ≤ value⁻¹ := (one_le_inv₀ valuePositive).mpr small
      have rootOrder : reference ≤ reference / value := by
        rw [le_div_iff₀ valuePositive]
        nlinarith
      have bounds : reference ≤ current ∧ current ≤ reference / value := by
        rcases between with first | second
        · exact ⟨rootOrder.trans first.2, first.1.trans rootOrder⟩
        · exact second
      rw [min_eq_left (by nlinarith : 1 ≤ value⁻¹ ^ 2),
        max_eq_right (by nlinarith : 1 ≤ value⁻¹ ^ 2), one_mul]
      constructor
      · nlinarith [sq_nonneg (current - reference)]
      · have squareBound : current ^ 2 ≤ (reference / value) ^ 2 := by
          nlinarith [sq_nonneg (current - reference / value)]
        simpa only [div_eq_mul_inv, mul_pow, mul_comm] using squareBound
    · have large : 1 ≤ value := le_of_lt (lt_of_not_ge small)
      have reciprocalSmall : value⁻¹ ≤ 1 := (inv_le_one₀ valuePositive).mpr large
      have rootOrder : reference / value ≤ reference := by
        rw [div_le_iff₀ valuePositive]
        nlinarith
      have bounds : reference / value ≤ current ∧ current ≤ reference := by
        rcases between with first | second
        · exact ⟨first.2, first.1⟩
        · exact ⟨rootOrder.trans second.1, second.2.trans rootOrder⟩
      rw [min_eq_right (by nlinarith : value⁻¹ ^ 2 ≤ 1),
        max_eq_left (by nlinarith : value⁻¹ ^ 2 ≤ 1), one_mul]
      constructor
      · have squareBound : (reference / value) ^ 2 ≤ current ^ 2 := by
          nlinarith [sq_nonneg (current - reference / value)]
        simpa only [div_eq_mul_inv, mul_pow, mul_comm] using squareBound
      · nlinarith [sq_nonneg (current - reference)]
  by_cases referenceNonnegative : 0 ≤ reference
  · exact nonnegativeReference referenceNonnegative interval
  · have negatedInterval : (-current - -reference) * (value * -current - -reference) ≤ 0 := by
      nlinarith [interval]
    simpa only [neg_sq] using nonnegativeReference (by linarith : 0 ≤ -reference) negatedInterval

theorem single_edge_minimizing_current_square_bounds
    (network : FiniteNetwork Vertex Edge) {resistance first second : Edge → ℝ}
    (changed : Edge) (resistancePositive : ∀ edge, 0 < resistance edge)
    (referenceValue : resistance changed = 1) {value : ℝ} (valuePositive : 0 < value)
    (firstFlow : first ∈ network.unitFlows) (secondFlow : second ∈ network.unitFlows)
    (firstMinimal : energy resistance first = network.effectiveResistance resistance)
    (secondMinimal : energy (Function.update resistance changed value) second =
      network.effectiveResistance (Function.update resistance changed value)) :
    min 1 (value⁻¹ ^ 2) * first changed ^ 2 ≤ second changed ^ 2 ∧
      second changed ^ 2 ≤ max 1 (value⁻¹ ^ 2) * first changed ^ 2 :=
  current_interval_square_bounds valuePositive
    (network.single_edge_minimizing_current_interval changed resistancePositive referenceValue
      valuePositive firstFlow secondFlow firstMinimal secondMinimal)

end
end IGSIII34.Resistance.FiniteNetwork
