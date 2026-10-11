import Universality.Percolation.AnnealedFiniteBirthMoments

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem hasSum_clusterFamily_size_weight (family : Finset (Finset (Fin vertices)))
    (weight : ℕ → ℝ) :
    HasSum (fun size : ℕ => weight size *
      ((family.filter fun cluster => cluster.card = size).card : ℝ))
      (∑ cluster ∈ family, weight cluster.card) := by
  rw [← clusterFamily_size_weight family weight]
  apply hasSum_sum_of_ne_finset_zero
  intro size hsize
  have hlarge : vertices < size := by
    simp only [Finset.mem_range] at hsize
    omega
  have hempty : (family.filter fun cluster => cluster.card = size) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro cluster _ heq
    have hcard : cluster.card ≤ vertices := by simpa using Finset.card_le_univ cluster
    omega
  simp [hempty]

theorem hasSum_size_internalClusterCount (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    HasSum (fun size : ℕ => (size : ℝ) * R.internalClusterCount configuration size)
      (R.internalClusterMass configuration : ℝ) := by
  simpa only [← R.internalClusterCount_eq_filter, internalClusterMass, Nat.cast_sum] using
    hasSum_clusterFamily_size_weight (R.internalClusterFamily configuration) (fun size => (size : ℝ))

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- The size-resolved graph decomposition also holds for the total mass,
configuration by configuration, before taking expectations. -/
theorem internalClusterMass_substitute (configuration : Fin outerEdges → Configuration innerEdges) :
    ((R.substitute S).internalClusterMass (substitutionConfigurationEquiv configuration) : ℝ) =
      (∑ edge, (S.internalClusterMass (configuration edge) : ℝ)) +
        ∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ) := by
  have hchildren := hasSum_sum (s := (Finset.univ : Finset (Fin outerEdges)))
    (fun edge _ => S.hasSum_size_internalClusterCount (configuration edge))
  have hborn := hasSum_clusterFamily_size_weight (R.birthClusterFamily S configuration)
    (fun size => (size : ℝ))
  have hsum := hchildren.add hborn
  apply ((R.substitute S).hasSum_size_internalClusterCount
    (substitutionConfigurationEquiv configuration)).unique
  apply hsum.congr_fun
  intro size
  rw [R.internalClusterCount_substitute S]
  push_cast
  simp only [birthClusterCount, mul_add, Finset.mul_sum]

/-- Newborn clusters use only top-level internal vertices and child boundary
mass. This exact accounting supplies a pathwise bound for every moment. -/
theorem birthClusterMass_boundary_partition (configuration : Fin outerEdges → Configuration innerEdges) :
    (∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ)) +
      (R.substitute S).internalSelectedMass true true (substitutionConfigurationEquiv configuration) =
      (outerVertices : ℝ) - 2 +
        ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) := by
  have hmass := R.internalClusterMass_substitute S configuration
  have hparent := (R.substitute S).internalClusterMass_partition (substitutionConfigurationEquiv configuration)
  have hchildren : (∑ edge : Fin outerEdges,
      ((S.internalClusterMass (configuration edge) : ℝ) +
        S.internalSelectedMass true true (configuration edge) + 2)) =
      ∑ _ : Fin outerEdges, (innerVertices : ℝ) := by
    apply Finset.sum_congr rfl
    intro edge _
    exact S.internalClusterMass_partition (configuration edge)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hchildren
  have hvertices := congrArg (fun n : ℕ => (n : ℝ)) (R.card_substitution_vertices S)
  push_cast [Nat.cast_sub S.two_le_vertices] at hvertices
  nlinarith

theorem birthClusterMass_le_child_boundary (configuration : Fin outerEdges → Configuration innerEdges) :
    (∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ)) ≤
      (outerVertices : ℝ) - 2 +
        ∑ edge, (S.internalSelectedMass true true (configuration edge) : ℝ) := by
  rw [← R.birthClusterMass_boundary_partition S configuration]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end
end Universality.FiniteNetwork
