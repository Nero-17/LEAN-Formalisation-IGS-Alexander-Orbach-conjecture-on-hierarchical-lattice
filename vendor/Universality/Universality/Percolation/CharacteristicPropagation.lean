import Universality.Percolation.AllClosedCharacteristic

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

/-- Unit modulus at a parent forces unit modulus in any child that occurs
with positive conditional probability. -/
theorem child_characteristic_unit_of_smoothing (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (state : LiveState) (values : LiveState → ℂ) (unit : ℂ)
    (hvalues : ∀ child, ‖values child‖ ≤ 1) (hunit : ‖unit‖ = 1)
    (hsmoothing : unit = ∑ coarse, (R.conditionalCellWeight p (state == .connected) coarse : ℂ) *
      ∏ e, match R.childState state coarse e with
        | none => 1
        | some child => values child)
    (coarse : Configuration edges) (edge : Fin edges) (child : LiveState)
    (hpositive : 0 < R.conditionalCellWeight p (state == .connected) coarse)
    (hchild : R.childState state coarse edge = some child) : ‖values child‖ = 1 := by
  classical
  let factor (configuration : Configuration edges) (e : Fin edges) : ℂ :=
    match R.childState state configuration e with
    | none => 1
    | some child => values child
  have hfactor (configuration : Configuration edges) (e : Fin edges) : ‖factor configuration e‖ ≤ 1 := by
    dsimp [factor]
    cases R.childState state configuration e with
    | none => simp
    | some child => exact hvalues child
  have hproduct (configuration : Configuration edges) : ‖∏ e, factor configuration e‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun e _ => hfactor configuration e)
  have heq := weighted_characteristic_eq_unit
    (R.conditionalCellWeight p (state == .connected)) (fun configuration => ∏ e, factor configuration e) unit
    (fun _ => R.conditionalCellWeight_nonneg hp.le hp'.le _ _)
    (R.sum_conditionalCellWeight p (by rwa [hfixed]) (by rwa [hfixed]) _)
    hproduct hunit hsmoothing.symm coarse hpositive
  have hle : ‖∏ e, factor coarse e‖ ≤ ‖factor coarse edge‖ := by
    rw [norm_prod]
    simpa using Finset.prod_le_prod_of_subset_of_le_one
      (s := {edge}) (t := Finset.univ) (f := fun e => ‖factor coarse e‖)
      (Finset.subset_univ _) (fun _ _ => norm_nonneg _) (fun e _ _ => hfactor coarse e)
  rw [heq, hunit] at hle
  have hvalue : factor coarse edge = values child := by simp only [factor, hchild]
  rw [hvalue] at hle
  exact le_antisymm (hvalues child) hle

end
end Universality.FiniteNetwork
