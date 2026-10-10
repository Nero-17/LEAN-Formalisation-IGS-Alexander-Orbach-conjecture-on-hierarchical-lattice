import Universality.Percolation.CharacteristicContraction
import Universality.Percolation.CharacteristicPropagation

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

/-- Unit modulus for an actual finite parent mass forces unit modulus for
any child occurring with positive conditional probability. The bounded reward
has unit phase and does not obstruct the argument. -/
theorem generation_child_characteristic_unit (rule : Rule) (hsymmetric : rule.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (t : ℝ) (state child : LiveState)
    (coarse : Configuration rule.edges) (edge : Fin rule.edges)
    (hpositive : 0 < rule.network.conditionalCellWeight p (state == .connected) coarse)
    (hchild : rule.network.childState state coarse edge = some child)
    (hunit : ‖(rule.generation (n + 1)).network.conditionalVertexCharacteristic p state t‖ = 1) :
    ‖(rule.generation n).network.conditionalVertexCharacteristic p child t‖ = 1 := by
  classical
  let values (child : LiveState) := (rule.generation n).network.conditionalVertexCharacteristic p child t
  let factor (configuration : Configuration rule.edges) (e : Fin rule.edges) : ℂ :=
    match rule.network.childState state configuration e with
    | none => 1
    | some child => values child
  let reward (configuration : Configuration rule.edges) :=
    Complex.exp ((t * rule.network.internalSelectedMass true (state == .both) configuration : ℝ) * Complex.I)
  have hvalues (child : LiveState) : ‖values child‖ ≤ 1 :=
    (rule.generation n).network.norm_conditionalInternalCharacteristic_le_one p hp.le hp'.le
      (by rwa [rule.generation_fixed_point p hfixed n]) (by rwa [rule.generation_fixed_point p hfixed n]) _ _ _ _
  have hfactor (configuration : Configuration rule.edges) (e : Fin rule.edges) : ‖factor configuration e‖ ≤ 1 := by
    dsimp [factor]
    cases rule.network.childState state configuration e with
    | none => simp
    | some child => exact hvalues child
  have hproduct (configuration : Configuration rule.edges) : ‖∏ e, factor configuration e‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun e _ => hfactor configuration e)
  have hreward (configuration : Configuration rule.edges) : ‖reward configuration‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have heq := weighted_characteristic_eq_unit
    (rule.network.conditionalCellWeight p (state == .connected))
    (fun configuration => reward configuration * ∏ e, factor configuration e)
    ((rule.generation (n + 1)).network.conditionalVertexCharacteristic p state t)
    (fun _ => rule.network.conditionalCellWeight_nonneg hp.le hp'.le _ _)
    (rule.network.sum_conditionalCellWeight p (by rwa [hfixed]) (by rwa [hfixed]) _)
    (fun configuration => by rw [norm_mul, hreward, one_mul]; exact hproduct configuration) hunit
    (by
      rw [rule.generation_conditionalVertexCharacteristic hsymmetric p hp hp' hfixed n state t]
      apply Finset.sum_congr rfl
      intro configuration _
      rw [mul_assoc]
      congr 1)
    coarse hpositive
  have hnorm := congrArg norm heq
  rw [norm_mul, hreward, one_mul, hunit] at hnorm
  have hle : ‖∏ e, factor coarse e‖ ≤ ‖factor coarse edge‖ := by
    rw [norm_prod]
    simpa using Finset.prod_le_prod_of_subset_of_le_one
      (s := {edge}) (t := Finset.univ) (f := fun e => ‖factor coarse e‖)
      (Finset.subset_univ _) (fun _ _ => norm_nonneg _) (fun e _ _ => hfactor coarse e)
  rw [hnorm] at hle
  have hvalue : factor coarse edge = values child := by simp only [factor, hchild]
  rw [hvalue] at hle
  exact le_antisymm (hvalues child) hle

end
end Universality.Rule
