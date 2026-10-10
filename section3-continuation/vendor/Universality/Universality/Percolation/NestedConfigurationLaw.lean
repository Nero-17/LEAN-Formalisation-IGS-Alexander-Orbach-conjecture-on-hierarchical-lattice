import Universality.Percolation.ConditionalSubstitutionLaw
import Universality.Probability.ThreeLevelProductLaw
import Universality.Percolation.VertexMassResponse

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def doubleConfigurationEquiv {edges : ℕ} :
    (Fin 4 → Fin 4 → Configuration edges) ≃ Configuration (4 * (4 * edges)) :=
  (Equiv.piCongrRight (fun _ : Fin 4 => substitutionConfigurationEquiv)).trans
    substitutionConfigurationEquiv

def tripleConfigurationEquiv {outerEdges edges : ℕ} :
    (Fin outerEdges → Fin 4 → Fin 4 → Configuration edges) ≃
      Configuration (outerEdges * (4 * (4 * edges))) :=
  (Equiv.piCongrRight (fun _ : Fin outerEdges => doubleConfigurationEquiv)).trans
    substitutionConfigurationEquiv

theorem tripleConfigurationEquiv_apply {outerEdges edges : ℕ}
    (cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges) :
    tripleConfigurationEquiv cells = substitutionConfigurationEquiv
      (fun edge => substitutionConfigurationEquiv (fun first => substitutionConfigurationEquiv (cells edge first))) := rfl

theorem bernoulliWeight_tripleConfiguration {outerEdges edges : ℕ} (p : ℝ)
    (cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges) :
    bernoulliWeight p (tripleConfigurationEquiv cells) =
      ∏ edge, ∏ first, ∏ second, bernoulliWeight p (cells edge first second) := by
  rw [tripleConfigurationEquiv_apply, bernoulliWeight_substitutionConfiguration]
  simp only [bernoulliWeight_substitutionConfiguration]

variable {vertices edges : ℕ} (S : FiniteNetwork vertices edges)

theorem crossing_probability_mul_conditionalWeight_le
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened : Bool) (cell : Configuration edges) :
    (if opened then S.reliability p else 1 - S.reliability p) *
      S.conditionalCellWeight p opened cell ≤ bernoulliWeight p cell := by
  have hne : (if opened then S.reliability p else 1 - S.reliability p) ≠ 0 := by
    cases opened
    · exact ne_of_gt (sub_pos.mpr hless)
    · exact ne_of_gt hpositive
  unfold conditionalCellWeight
  rw [mul_div_cancel₀ _ hne]
  split
  · exact le_rfl
  · exact bernoulliWeight_nonneg hp hp' cell

theorem triple_conditional_selected_mass {outerEdges : ℕ}
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (edge : Fin outerEdges) (hopened : coarse edge = true) :
    (∑ cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges,
      (∏ e, ∏ first, ∏ second, S.conditionalCellWeight p (coarse e) (cells e first second)) *
        (S.internalSelectedMass true false (cells edge 0 1) : ℝ)) = S.conditionalVertexMass p .connected := by
  rw [three_level_product_local_moment
    (fun e (_ : Fin 4) (_ : Fin 4) cell => S.conditionalCellWeight p (coarse e) cell)
    (fun e _ _ => S.sum_conditionalCellWeight p hpositive hless (coarse e))
    (fun cell => (S.internalSelectedMass true false cell : ℝ)) edge 0 1]
  rw [hopened]
  rfl

end
end Universality.FiniteNetwork


