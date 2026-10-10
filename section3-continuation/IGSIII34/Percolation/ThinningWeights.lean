import IGSIII34.Percolation.BernoulliThinning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork

theorem conditioned_bernoulli_thinning_split {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (parameter retention : ℝ) :
    (∑ configuration : Configuration edges, rule.conditionalCellWeight parameter true configuration *
      ∑ marking : Configuration edges, bernoulliWeight retention marking *
        (if rule.crosses (fun edge => configuration edge && marking edge) then 1 else 0)) =
          rule.reliability (parameter * retention) / rule.reliability parameter := by
  classical
  let split : (Fin edges → Bool × Bool) ≃ Configuration edges × Configuration edges :=
    { toFun := fun bits => (fun edge => (bits edge).1, fun edge => (bits edge).2)
      invFun := fun pair edge => (pair.1 edge, pair.2 edge)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let response : Configuration edges × Configuration edges → ℝ := fun pair =>
    rule.conditionalCellWeight parameter true pair.1 * bernoulliWeight retention pair.2 *
      (if rule.crosses (fun edge => pair.1 edge && pair.2 edge) then 1 else 0)
  calc
    _ = ∑ pair, response pair := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro configuration _
      dsimp [response]
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = ∑ bits : Fin edges → Bool × Bool, response (split bits) := (split.sum_comp response).symm
    _ = ∑ bits : Fin edges → Bool × Bool,
        ((if rule.crosses (fun edge => (bits edge).1) then
          (∏ edge, bernoulliPairWeight parameter retention (bits edge)) else 0) /
          rule.reliability parameter) *
          (if rule.crosses (fun edge => (bits edge).1 && (bits edge).2) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro bits _
      have productIdentity : (∏ edge, bernoulliPairWeight parameter retention (bits edge)) =
          bernoulliWeight parameter (fun edge => (bits edge).1) *
          bernoulliWeight retention (fun edge => (bits edge).2) := by
        simp only [bernoulliPairWeight, bernoulliWeight, Finset.prod_mul_distrib]
      rw [productIdentity]
      dsimp [response, split, conditionalCellWeight]
      cases crossing : rule.crosses (fun edge => (bits edge).1) <;> simp [crossing] <;> ring
    _ = _ := conditioned_bernoulli_thinning rule parameter retention

end
end IGSIII34.Percolation
