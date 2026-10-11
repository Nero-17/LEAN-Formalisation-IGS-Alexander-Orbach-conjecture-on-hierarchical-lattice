import Universality.Percolation.CoarseRootLaw
import Universality.Percolation.BirthMomentUpper

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem internalSelectedMass_le_boundary (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges) :
    R.internalSelectedMass sourceSelected targetSelected configuration ≤
      R.internalSelectedMass true true configuration := by
  unfold internalSelectedMass
  apply Finset.sum_le_sum
  intro vertex _
  unfold selectedActive
  cases sourceSelected <;> cases targetSelected <;>
    cases (R.openGraph configuration).reachableDecide R.source vertex.val <;>
    cases (R.openGraph configuration).reachableDecide R.target vertex.val <;> decide

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem coarseRoot_cluster_mass_le_boundary
    (configuration : Fin outerEdges → Configuration innerEdges) (root : Fin outerVertices) :
    ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card ≤
      outerVertices + ∑ edge, S.internalSelectedMass true true (configuration edge) := by
  rw [R.coarseRoot_cluster_mass S]
  apply Nat.add_le_add
  · simpa only [Fintype.card_fin] using Finset.card_le_univ (R.clusterVertices (S.coarseConfiguration configuration) root)
  · apply Finset.sum_le_sum
    intro edge _
    exact S.internalSelectedMass_le_boundary _ _ _

theorem coarseRoot_cluster_power_le_boundary
    (configuration : Fin outerEdges → Configuration innerEdges) (root : Fin outerVertices)
    (order : ℕ) (horder : 1 ≤ order) :
    (((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) ).card : ℝ) ^ order ≤
      ((outerEdges : ℝ) + 1) ^ (order - 1) *
        ((outerVertices : ℝ) ^ order +
          ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) ^ order) := by
  have hbound : (((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card : ℝ) ≤
      (outerVertices : ℝ) + ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) := by
    exact_mod_cast R.coarseRoot_cluster_mass_le_boundary S configuration root
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hbound order).trans
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

theorem coarseRootMassObservable_power_le_boundary_moment
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (root : Fin outerVertices)
    (order : ℕ) (horder : 1 ≤ order) :
    R.coarseRootMassObservable S p root (fun mass => (mass : ℝ) ^ order) ≤
      ((outerEdges : ℝ) + 1) ^ (order - 1) *
        ((outerVertices : ℝ) ^ order + (outerEdges : ℝ) * S.expectedInternalBoundaryMoment p order) := by
  unfold coarseRootMassObservable
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [bernoulliWeight_substitutionConfiguration]
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
      exact mul_le_mul_of_nonneg_left (R.coarseRoot_cluster_power_le_boundary S configuration root order horder)
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

end
end Universality.FiniteNetwork

