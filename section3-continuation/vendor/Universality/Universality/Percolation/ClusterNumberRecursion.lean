import Universality.Percolation.InternalClusterChoices
import Universality.Percolation.ConditionalSubstitutionLaw

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem clusters_avoiding_coarse_card (configuration : Fin outerEdges → Configuration innerEdges) :
    (((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
      fun cluster => Disjoint cluster (R.coarseVertices S)).card =
      ∑ edge, (S.internalClusterFamily (configuration edge)).card := by
  classical
  rw [← R.internalClusterChoiceImage_range S configuration,
    Finset.card_image_of_injective _ (R.internalClusterChoiceImage_injective S configuration), Finset.card_univ]
  change Fintype.card (Σ edge : Fin outerEdges, {cluster // cluster ∈ S.internalClusterFamily (configuration edge)}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]

/-- Exact pathwise decomposition of all fine clusters into untouched internal
child clusters and clusters represented in the coarse graph. -/
theorem clusterFamily_substitute_card (configuration : Fin outerEdges → Configuration innerEdges) :
    ((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).card =
      (R.clusterFamily (S.coarseConfiguration configuration)).card +
        ∑ edge, (S.internalClusterFamily (configuration edge)).card := by
  classical
  have hfilter : (((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
      fun cluster => ¬ Disjoint cluster (R.coarseVertices S)) = R.coarseTouchedClusters S configuration := by
    rw [R.coarseTouchedClusters_eq]
    ext cluster
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    rw [Finset.not_disjoint_iff]
    constructor <;> rintro ⟨vertex, hfirst, hsecond⟩ <;> exact ⟨vertex, hsecond, hfirst⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration))
    (p := fun cluster => Disjoint cluster (R.coarseVertices S))
  rw [R.clusters_avoiding_coarse_card S configuration, hfilter,
    R.coarseTouchedClusters_card S configuration] at hsplit
  omega

def expectedClusterNumber (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * (R.clusterFamily configuration).card

def expectedInternalClusterNumber (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * (R.internalClusterFamily configuration).card

/-- The finite-volume renormalisation equation for the genuine cluster count. -/
theorem expectedClusterNumber_substitute (p : ℝ) :
    (R.substitute S).expectedClusterNumber p =
      R.expectedClusterNumber (S.reliability p) + (outerEdges : ℝ) * S.expectedInternalClusterNumber p := by
  unfold expectedClusterNumber
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.clusterFamily_substitute_card S, bernoulliWeight_substitutionConfiguration,
    Nat.cast_add, Nat.cast_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact S.coarse_expectation p (fun coarse => (R.clusterFamily coarse).card)
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hlocal (edge : Fin outerEdges) :
        (∑ configuration : Fin outerEdges → Configuration innerEdges,
          (∏ e, bernoulliWeight p (configuration e)) *
            (S.internalClusterFamily (configuration edge)).card) = S.expectedInternalClusterNumber p := by
      rw [Universality.finite_product_local_moment
        (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
        (fun cell => ((S.internalClusterFamily cell).card : ℝ)) edge]
      simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul]
      rfl
    simp_rw [hlocal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end Universality.FiniteNetwork
