import Universality.Percolation.GenerationMassCharacteristic
import Universality.Percolation.MassRowLowerBounds

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

theorem norm_conditionalInternalCharacteristic_le_one (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (t : ℝ) :
    ‖R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t‖ ≤ 1 := by
  unfold conditionalInternalCharacteristic
  calc
    _ ≤ ∑ ω, ‖(R.conditionalCellWeight p opened ω : ℂ) *
      Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected ω : ℝ) * Complex.I)‖ := norm_sum_le _ _
    _ = ∑ ω, R.conditionalCellWeight p opened ω := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (R.conditionalCellWeight_nonneg hp hp' opened ω)]
    _ = 1 := R.sum_conditionalCellWeight p hpositive hless opened

/-- Every source-incident edge remains live. These factors give a genuine
power contraction in Fourier modulus for every coarse configuration. -/
theorem norm_child_characteristic_product_le (R : FiniteNetwork vertices edges)
    (state : LiveState) (coarse : Configuration edges) (values : LiveState → ℂ)
    (bound : ℝ) (hbound : bound ≤ 1) (hvalues : ∀ child, ‖values child‖ ≤ bound) :
    ‖∏ e, match R.childState state coarse e with
        | none => (1 : ℂ)
        | some child => values child‖ ≤ bound ^ R.sourceIncidentEdges.card := by
  classical
  let factor (e : Fin edges) : ℂ := match R.childState state coarse e with
    | none => 1
    | some child => values child
  change ‖∏ e, factor e‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ ∏ e ∈ R.sourceIncidentEdges, ‖factor e‖ :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
        (fun _ _ => norm_nonneg _)
        (fun e _ _ => by
          dsimp [factor]
          cases R.childState state coarse e with
          | none => simp
          | some child => exact (hvalues child).trans hbound)
    _ ≤ ∏ _e ∈ R.sourceIncidentEdges, bound := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro e he
      have hne := R.childState_incident_ne_none state coarse e he
      dsimp [factor]
      cases hchild : R.childState state coarse e with
      | none => exact (hne hchild).elim
      | some child => exact hvalues child
    _ = _ := Finset.prod_const _

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Exact finite-depth Fourier contraction by the actual terminal degree. -/
theorem generation_characteristic_norm_bound (rule : Rule) (hsymmetric : rule.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (t bound : ℝ) (hbound : bound ≤ 1)
    (hvalues : ∀ child, ‖(rule.generation n).network.conditionalVertexCharacteristic p child t‖ ≤ bound)
    (state : LiveState) :
    ‖(rule.generation (n + 1)).network.conditionalVertexCharacteristic p state t‖ ≤
      bound ^ rule.network.sourceIncidentEdges.card := by
  rw [rule.generation_conditionalVertexCharacteristic hsymmetric p hp hp' hfixed]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ coarse, rule.network.conditionalCellWeight p (state == .connected) coarse *
        bound ^ rule.network.sourceIncidentEdges.card := by
      apply Finset.sum_le_sum
      intro coarse _
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (rule.network.conditionalCellWeight_nonneg hp.le hp'.le _ _)]
      exact mul_le_mul_of_nonneg_left
        (rule.network.norm_child_characteristic_product_le state coarse
          (fun child => (rule.generation n).network.conditionalVertexCharacteristic p child t)
          bound hbound hvalues)
        (rule.network.conditionalCellWeight_nonneg hp.le hp'.le _ _)
    _ = _ := by
      rw [← Finset.sum_mul, rule.network.sum_conditionalCellWeight p (by rwa [hfixed])
        (by rwa [hfixed]), one_mul]

end
end Universality.Rule
