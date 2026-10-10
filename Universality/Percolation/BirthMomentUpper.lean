import Universality.Percolation.BirthMassPathwise
import Universality.Percolation.BoundaryMassMoments
import Mathlib.Analysis.MeanInequalities

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem finite_sum_power_le_power_sum {α : Type*} (s : Finset α) (value : α → ℝ)
    (hvalue : ∀ a ∈ s, 0 ≤ value a) (order : ℕ) (horder : 1 ≤ order) :
    ∑ a ∈ s, value a ^ order ≤ (∑ a ∈ s, value a) ^ order := by
  have hpred : order - 1 + 1 = order := by omega
  calc
    _ = ∑ a ∈ s, value a * value a ^ (order - 1) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← pow_succ', hpred]
    _ ≤ ∑ a ∈ s, value a * (∑ b ∈ s, value b) ^ (order - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hvalue a ha) (Finset.single_le_sum hvalue ha) _) (hvalue a ha)
    _ = _ := by rw [← Finset.sum_mul, ← pow_succ', hpred]

namespace FiniteNetwork
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem birthClusterPower_le_child_boundary (configuration : Fin outerEdges → Configuration innerEdges)
    (order : ℕ) (horder : 1 ≤ order) :
    (∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ) ^ order) ≤
      ((outerEdges : ℝ) + 1) ^ (order - 1) *
        ((outerVertices : ℝ) ^ order +
          ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order) := by
  have hmass := R.birthClusterMass_le_child_boundary S configuration
  have hsum := finite_sum_power_le_power_sum (R.birthClusterFamily S configuration)
    (fun cluster => (cluster.card : ℝ)) (fun _ _ => Nat.cast_nonneg _) order horder
  have hbound : (∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ)) ≤
      (outerVertices : ℝ) + ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) := by
    linarith
  apply hsum.trans ((pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hbound order).trans ?_)
  let value : Option (Fin outerEdges) → ℝ := fun index =>
    match index with
    | none => outerVertices
    | some edge => S.internalSelectedMass true true (configuration edge)
  have hvalue (index : Option (Fin outerEdges)) : 0 ≤ value index := by
    cases index <;> exact Nat.cast_nonneg _
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ (f := value)
    (p := (order : ℝ)) (by exact_mod_cast horder) (fun index _ => hvalue index)
  have hcast : (order : ℝ) - 1 = ((order - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub horder, Nat.cast_one]
  rw [hcast] at hholder
  simpa only [Real.rpow_natCast, Fintype.sum_option,
    Finset.card_univ, Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one, value] using hholder

theorem expectedBirthClusterPower_le_boundary_moment {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (order : ℕ) (horder : 1 ≤ order) :
    R.expectedBirthClusterPower S p order ≤
      ((outerEdges : ℝ) + 1) ^ (order - 1) *
        ((outerVertices : ℝ) ^ order + (outerEdges : ℝ) * S.expectedInternalBoundaryMoment p order) := by
  unfold expectedBirthClusterPower
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, bernoulliWeight_substitutionConfiguration]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) *
          (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order) =
        S.expectedInternalBoundaryMoment p order := by
    rw [finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => (S.internalSelectedMass true true cell : ℝ) ^ order) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul, expectedInternalBoundaryMoment]
  have hweights : (∑ configuration : Fin outerEdges → Configuration innerEdges,
      ∏ e, bernoulliWeight p (configuration e)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [sum_bernoulliWeight, Finset.prod_const_one]
  calc
    _ ≤ ∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) *
          (((outerEdges : ℝ) + 1) ^ (order - 1) * ((outerVertices : ℝ) ^ order +
            ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order)) := by
      apply Finset.sum_le_sum
      intro configuration _
      exact mul_le_mul_of_nonneg_left (R.birthClusterPower_le_child_boundary S configuration order horder)
        (Finset.prod_nonneg (fun _ _ => bernoulliWeight_nonneg hp hp' _))
    _ = _ := by
      have hfactor (configuration : Fin outerEdges → Configuration innerEdges) :
          (∏ e, bernoulliWeight p (configuration e)) *
            (((outerEdges : ℝ) + 1) ^ (order - 1) * ((outerVertices : ℝ) ^ order +
              ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order)) =
          ((outerEdges : ℝ) + 1) ^ (order - 1) *
            ((∏ e, bernoulliWeight p (configuration e)) * ((outerVertices : ℝ) ^ order +
              ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order)) := by ring
      simp_rw [hfactor]
      rw [← Finset.mul_sum]
      congr 1
      simp only [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hweights, one_mul]
      congr 1
      rw [Finset.sum_comm]
      simp only [hlocal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end FiniteNetwork
end
end Universality
