import Universality.Percolation.BirthRootPointBounds

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Every birth component has an old interior vertex, so outer-terminal roots can be omitted. -/
theorem birthClusterCount_le_interiorRoot_count
    (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) :
    R.birthClusterCount S configuration size ≤
      ∑ root : R.InteriorVertex,
        if ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
          (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root.val))).card = size then 1 else 0 := by
  let roots := Finset.univ.filter fun root : R.InteriorVertex =>
    ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root.val))).card = size
  have hsubset : (R.birthClusterFamily S configuration).filter (fun cluster => cluster.card = size) ⊆
      roots.image (fun root => (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root.val))) := by
    intro cluster hcluster
    obtain ⟨hbirth, hsize⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨hinternal, htouch⟩ := Finset.mem_filter.mp hbirth
    obtain ⟨hfamily, hsource, htarget⟩ := Finset.mem_filter.mp hinternal
    obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp htouch
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcoarse
    have hroot : root ≠ R.source ∧ root ≠ R.target := by
      constructor
      · intro heq
        subst root
        exact hsource hvertex
      · intro heq
        subst root
        exact htarget hvertex
    have heq := (R.substitute S).clusterVertices_eq_of_mem _ cluster hfamily _ hvertex
    exact Finset.mem_image.mpr ⟨⟨root, hroot⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [heq]; exact hsize⟩, heq⟩
  calc
    _ ≤ (roots.image (fun root => (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root.val)))).card := Finset.card_le_card hsubset
    _ ≤ roots.card := Finset.card_image_le
    _ = _ := by simp only [roots, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem expectedBirthClusterCount_le_interiorRoot_laws
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    R.expectedBirthClusterCount S p size ≤
      ∑ root : R.InteriorVertex, R.coarseRootMassObservable S p root.val (fun mass => if mass = size then 1 else 0) := by
  unfold expectedBirthClusterCount coarseRootMassObservable
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro configuration _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
  have h := R.birthClusterCount_le_interiorRoot_count S (substitutionConfigurationEquiv.symm configuration) size
  simp only [Equiv.apply_symm_apply] at h
  change (R.birthClusterCount S (substitutionConfigurationEquiv.symm configuration) size : ℝ) ≤
    ∑ root : R.InteriorVertex, if ((R.substitute S).clusterVertices configuration
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root.val))).card = size then (1 : ℝ) else 0
  exact_mod_cast h

end
end Universality.FiniteNetwork

