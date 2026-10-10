import IGSIII.Chemical.SubstitutionPaths.FiveCycleActual
import IGSIII.Chemical.SubstitutionPaths.InverseCube
import IGSIII.Chemical.SubstitutionPaths.ConnectedProductLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII.Chemical.FiveCycle

open Universality Universality.FiniteNetwork Substitution IGSIII.Probability
open scoped BigOperators

theorem bernoulli_all_open_probability {edges : ℕ} (p : ℝ) (path : Finset (Fin edges)) :
    (∑ configuration : Configuration edges, bernoulliWeight p configuration *
      (if ∀ edge ∈ path, configuration edge = true then 1 else 0)) = p ^ path.card := by
  classical
  have factor (configuration : Configuration edges) :
      bernoulliWeight p configuration * (if ∀ edge ∈ path, configuration edge = true then 1 else 0) =
        ∏ edge, (if configuration edge then p else 1 - p) *
          (if edge ∈ path then (if configuration edge then 1 else 0) else 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_boole]
    simp only [bernoulliWeight]
    split_ifs <;> rfl
  simp_rw [factor]
  rw [← Fintype.prod_sum (fun (edge : Fin edges) (opened : Bool) =>
    (if opened then p else 1 - p) * (if edge ∈ path then (if opened then 1 else 0) else 1))]
  have coordinateSum (edge : Fin edges) :
      (∑ opened : Bool, (if opened then p else 1 - p) *
        (if edge ∈ path then (if opened then 1 else 0) else 1)) =
          if edge ∈ path then p else 1 := by by_cases member : edge ∈ path <;> simp [member]
  simp_rw [coordinateSum]
  rw [Finset.prod_ite_mem_eq]
  simp

theorem conditioned_branch_probability (p : ℝ) (fixedPoint : network.reliability p = p)
    (path : Finset (Fin 5))
    (crosses : ∀ configuration : Configuration 5,
      (∀ edge ∈ path, configuration edge = true) → network.crosses configuration = true) :
    (∑ configuration, network.conditionalCellWeight p true configuration *
      (if ∀ edge ∈ path, configuration edge = true then 1 else 0)) = p ^ path.card / p := by
  classical
  calc
    _ = (∑ configuration : Configuration 5, bernoulliWeight p configuration *
        (if ∀ edge ∈ path, configuration edge = true then 1 else 0)) / p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro configuration _
      by_cases retained : ∀ edge ∈ path, configuration edge = true
      · simp only [if_pos retained, mul_one, conditionalCellWeight,
          crosses configuration retained, fixedPoint, if_true]
      · simp [retained]
    _ = _ := by rw [bernoulli_all_open_probability]

theorem short_branch_probability (p : ℝ) (positive : 0 < p)
    (fixedPoint : network.reliability p = p) :
    (∑ configuration, network.conditionalCellWeight p true configuration *
      (if configuration 0 && configuration 1 then 1 else 0)) = p := by
  have probability := conditioned_branch_probability p fixedPoint {0, 1} (by
    intro configuration retained
    rw [crosses_iff_branches]
    simp only [Finset.mem_insert, Finset.mem_singleton] at retained
    simp [retained 0 (Or.inl rfl), retained 1 (Or.inr rfl)])
  simpa [sq, positive.ne', Finset.mem_insert, Finset.mem_singleton, Bool.and_eq_true] using probability

theorem long_branch_probability (p : ℝ) (positive : 0 < p)
    (fixedPoint : network.reliability p = p) :
    (∑ configuration, network.conditionalCellWeight p true configuration *
      (if configuration 2 && configuration 3 && configuration 4 then 1 else 0)) = p ^ 2 := by
  have probability := conditioned_branch_probability p fixedPoint {2, 3, 4} (by
    intro configuration retained
    rw [crosses_iff_branches]
    simp only [Finset.mem_insert, Finset.mem_singleton] at retained
    simp [retained 2 (Or.inl rfl), retained 3 (Or.inr (Or.inl rfl)), retained 4 (Or.inr (Or.inr rfl))])
  have cardinality : ({2, 3, 4} : Finset (Fin 5)).card = 3 := by decide
  rw [cardinality] at probability
  have quotient : p ^ 3 / p = p ^ 2 := by field_simp
  rw [quotient] at probability
  simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Bool.and_eq_true, and_assoc] using probability

private theorem short_sum (value : Fin 5 → ℝ) :
    (∑ edge ∈ ({0, 1} : Finset (Fin 5)), value edge) = value 0 + value 1 := by simp

private theorem long_sum (value : Fin 5 → ℝ) :
    (∑ edge ∈ ({2, 3, 4} : Finset (Fin 5)), value edge) = value 2 + value 3 + value 4 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem actual_path_inverse_cube_bound (configuration : Configuration 5)
    (crossing : network.crosses configuration = true) (value : Fin 5 → ℝ)
    (positive : ∀ edge, 0 < value edge) :
    ((edgePathFamily network configuration).shortest value)⁻¹ ^ 3 ≤
      (if configuration 0 && configuration 1 then (1 / 16 : ℝ) * ((value 0)⁻¹ ^ 3 + (value 1)⁻¹ ^ 3) else 0) +
      (if configuration 2 && configuration 3 && configuration 4 then
        (1 / 81 : ℝ) * ((value 2)⁻¹ ^ 3 + (value 3)⁻¹ ^ 3 + (value 4)⁻¹ ^ 3) else 0) := by
  obtain ⟨path, membership, minimal⟩ := (edgePathFamily network configuration).exists_minimizer value
  obtain ⟨branches, retained⟩ := (actual_path_iff_branches configuration crossing path).mp membership
  have positiveZero := positive 0
  have positiveOne := positive 1
  have positiveTwo := positive 2
  have positiveThree := positive 3
  have positiveFour := positive 4
  have shortNonnegative : 0 ≤ (if configuration 0 && configuration 1 then
      (1 / 16 : ℝ) * ((value 0)⁻¹ ^ 3 + (value 1)⁻¹ ^ 3) else 0) := by split <;> positivity
  have longNonnegative : 0 ≤ (if configuration 2 && configuration 3 && configuration 4 then
      (1 / 81 : ℝ) * ((value 2)⁻¹ ^ 3 + (value 3)⁻¹ ^ 3 + (value 4)⁻¹ ^ 3) else 0) := by split <;> positivity
  rcases branches with short | long
  · subst path
    have shortOpen : (configuration 0 && configuration 1) = true := by
      simp [retained 0 (by simp), retained 1 (by simp)]
    have inverseBound := inverse_cube_sum ({0, 1} : Finset (Fin 5)) (by simp) value
      (fun edge _ => positive edge)
    simp only [PathFamily.pathCost, short_sum] at minimal inverseBound
    norm_num at inverseBound
    rw [minimal]
    simp only [if_pos shortOpen]
    exact (show (value 0 + value 1)⁻¹ ^ 3 ≤
      (1 / 16 : ℝ) * ((value 0)⁻¹ ^ 3 + (value 1)⁻¹ ^ 3) by
        simpa only [inv_pow] using inverseBound).trans (le_add_of_nonneg_right longNonnegative)
  · subst path
    have longOpen : (configuration 2 && configuration 3 && configuration 4) = true := by
      simp [retained 2 (by simp), retained 3 (by simp), retained 4 (by simp)]
    have inverseBound := inverse_cube_sum ({2, 3, 4} : Finset (Fin 5)) (by simp) value
      (fun edge _ => positive edge)
    have cardinality : ({2, 3, 4} : Finset (Fin 5)).card = 3 := by decide
    simp only [PathFamily.pathCost, long_sum, cardinality] at minimal inverseBound
    norm_num at inverseBound
    rw [minimal]
    simp only [if_pos longOpen]
    exact (show (value 2 + value 3 + value 4)⁻¹ ^ 3 ≤
      (1 / 81 : ℝ) * ((value 2)⁻¹ ^ 3 + (value 3)⁻¹ ^ 3 + (value 4)⁻¹ ^ 3) by
        simpa only [inv_pow] using inverseBound).trans (le_add_of_nonneg_left shortNonnegative)

end IGSIII.Chemical.FiveCycle
