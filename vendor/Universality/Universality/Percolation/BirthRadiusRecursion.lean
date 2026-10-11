import Universality.Percolation.ClusterRadius
import Universality.Percolation.AnnealedFiniteBirthMoments

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def birthRadiusRootCount (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges) (radius : ℕ) : ℕ :=
  ∑ cluster ∈ R.birthClusterFamily S configuration,
    (R.substitute S).clusterRadiusRootCount cluster radius

def expectedInternalRadiusRootCount (R : FiniteNetwork vertices edges) (p : ℝ) (radius : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalRadiusRootCount configuration radius

def expectedBirthRadiusRootCount (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) (radius : ℕ) : ℝ :=
  ∑ configuration : Configuration (outerEdges * innerEdges), bernoulliWeight p configuration *
    R.birthRadiusRootCount S (substitutionConfigurationEquiv.symm configuration) radius

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem clusters_avoiding_coarse_radiusRootCount
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges) (radius : ℕ) :
    (∑ cluster ∈ ((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
      (fun cluster => Disjoint cluster (R.coarseVertices S)),
      (R.substitute S).clusterRadiusRootCount cluster radius) =
      ∑ edge, S.internalRadiusRootCount (configuration edge) radius := by
  classical
  rw [← R.internalClusterChoiceImage_range S configuration, Finset.sum_image]
  · change (∑ choice : S.InternalClusterChoices configuration,
      (R.substitute S).clusterRadiusRootCount (R.internalClusterChoiceImage S configuration choice) radius) = _
    simp only [internalClusterChoiceImage, R.substitute_cell_clusterRadiusRootCount S hinner]
    change (∑ choice : (Σ edge : Fin outerEdges, {cluster // cluster ∈ S.internalClusterFamily (configuration edge)}),
      S.clusterRadiusRootCount choice.2.val radius) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro edge _
    exact Finset.sum_coe_sort (S.internalClusterFamily (configuration edge))
      (fun cluster => S.clusterRadiusRootCount cluster radius)
  · intro first _ second _ heq
    exact R.internalClusterChoiceImage_injective S configuration heq

theorem internalRadiusRootCount_substitute
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges) (radius : ℕ) :
    (R.substitute S).internalRadiusRootCount (substitutionConfigurationEquiv configuration) radius =
      (∑ edge, S.internalRadiusRootCount (configuration edge) radius) +
        R.birthRadiusRootCount S configuration radius := by
  classical
  have hsource : (R.substitute S).source ∈ R.coarseVertices S :=
    Finset.mem_image.mpr ⟨R.source, Finset.mem_univ _, rfl⟩
  have htarget : (R.substitute S).target ∈ R.coarseVertices S :=
    Finset.mem_image.mpr ⟨R.target, Finset.mem_univ _, rfl⟩
  have havoiding : ((R.substitute S).internalClusterFamily (substitutionConfigurationEquiv configuration)).filter
      (fun cluster => Disjoint cluster (R.coarseVertices S)) =
      ((R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration)).filter
        (fun cluster => Disjoint cluster (R.coarseVertices S)) := by
    ext cluster
    simp only [internalClusterFamily, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hf, _, _⟩, hd⟩; exact ⟨hf, hd⟩
    · rintro ⟨hf, hd⟩
      exact ⟨⟨hf, fun hs => Finset.disjoint_left.mp hd hs hsource,
        fun ht => Finset.disjoint_left.mp hd ht htarget⟩, hd⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (R.substitute S).internalClusterFamily (substitutionConfigurationEquiv configuration))
    (p := fun cluster => Disjoint cluster (R.coarseVertices S))
    (f := fun cluster => (R.substitute S).clusterRadiusRootCount cluster radius)
  rw [havoiding, R.clusters_avoiding_coarse_radiusRootCount S hinner configuration radius] at hsplit
  exact hsplit.symm

theorem expectedInternalRadiusRootCount_substitute
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex) (p : ℝ) (radius : ℕ) :
    (R.substitute S).expectedInternalRadiusRootCount p radius =
      (outerEdges : ℝ) * S.expectedInternalRadiusRootCount p radius +
        R.expectedBirthRadiusRootCount S p radius := by
  unfold expectedInternalRadiusRootCount expectedBirthRadiusRootCount
  rw [← substitutionConfigurationEquiv.sum_comp]
  conv_rhs => rhs; rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalRadiusRootCount_substitute S hinner, Equiv.symm_apply_apply,
    bernoulliWeight_substitutionConfiguration, Nat.cast_add, Nat.cast_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) * (S.internalRadiusRootCount (configuration edge) radius : ℝ)) =
      ∑ configuration, bernoulliWeight p configuration * (S.internalRadiusRootCount configuration radius : ℝ) := by
    rw [Universality.finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => (S.internalRadiusRootCount cell radius : ℝ)) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul]
  simp_rw [hlocal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem expectedBirthRadiusRootCount_le_mass {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    R.expectedBirthRadiusRootCount S p radius ≤ R.expectedBirthClusterPower S p 1 := by
  unfold expectedBirthRadiusRootCount expectedBirthClusterPower birthRadiusRootCount
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' configuration)
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro cluster _
  rw [pow_one]
  exact_mod_cast (R.substitute S).clusterRadiusRootCount_le_card cluster radius

end
end Universality.FiniteNetwork
