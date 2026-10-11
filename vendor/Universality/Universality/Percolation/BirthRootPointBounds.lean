import Universality.Percolation.CoarseRootLaw

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Counting all coarse roots can overcount a birth cluster, but never misses one. -/
theorem birthClusterCount_le_coarseRoot_count
    (configuration : Fin outerEdges → Configuration innerEdges) (size : ℕ) :
    R.birthClusterCount S configuration size ≤
      ∑ root : Fin outerVertices,
        if ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
          (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card = size then 1 else 0 := by
  let roots := Finset.univ.filter fun root : Fin outerVertices =>
    ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card = size
  have hsubset : (R.birthClusterFamily S configuration).filter (fun cluster => cluster.card = size) ⊆
      roots.image (fun root => (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))) := by
    intro cluster hcluster
    obtain ⟨hbirth, hsize⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨hinternal, htouch⟩ := Finset.mem_filter.mp hbirth
    have hfamily := (Finset.mem_filter.mp hinternal).1
    obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp htouch
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcoarse
    have heq := (R.substitute S).clusterVertices_eq_of_mem _ cluster hfamily _ hvertex
    exact Finset.mem_image.mpr ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [heq]; exact hsize⟩, heq⟩
  calc
    _ ≤ (roots.image (fun root => (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)))).card := Finset.card_le_card hsubset
    _ ≤ roots.card := Finset.card_image_le
    _ = _ := by simp only [roots, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem coarseRoot_atom_le_birthClusterCount
    (configuration : Fin outerEdges → Configuration innerEdges) (root : Fin outerVertices)
    (hroot : R.source ∉ R.clusterVertices (S.coarseConfiguration configuration) root ∧
      R.target ∉ R.clusterVertices (S.coarseConfiguration configuration) root) (size : ℕ) :
    (if ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card = size then 1 else 0) ≤
      R.birthClusterCount S configuration size := by
  split_ifs with hsize
  · exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr
      ⟨(R.coarseRoot_cluster_mem_birth_iff S configuration root).mpr hroot, hsize⟩⟩
  · exact Nat.zero_le _

/-- Actual finite birth size probabilities are bounded by a fixed finite sum of coarse-root laws. -/
theorem expectedBirthClusterCount_le_coarseRoot_laws
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    R.expectedBirthClusterCount S p size ≤
      ∑ root : Fin outerVertices, R.coarseRootMassObservable S p root (fun mass => if mass = size then 1 else 0) := by
  unfold expectedBirthClusterCount coarseRootMassObservable
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro configuration _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
  have h := R.birthClusterCount_le_coarseRoot_count S (substitutionConfigurationEquiv.symm configuration) size
  simp only [Equiv.apply_symm_apply] at h
  change (R.birthClusterCount S (substitutionConfigurationEquiv.symm configuration) size : ℝ) ≤
    ∑ root : Fin outerVertices, if ((R.substitute S).clusterVertices configuration
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card = size then (1 : ℝ) else 0
  exact_mod_cast h

theorem expectedBirthClusterCount_ge_coarseRoot_branch
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (coarse : Configuration outerEdges) (root : Fin outerVertices)
    (hroot : R.source ∉ R.clusterVertices coarse root ∧ R.target ∉ R.clusterVertices coarse root)
    (size : ℕ) :
    bernoulliWeight (S.reliability p) coarse *
      (∑ cells : Fin outerEdges → Configuration innerEdges,
        (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
          if (R.clusterVertices coarse root).card +
            ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge) = size
          then 1 else 0) ≤ R.expectedBirthClusterCount S p size := by
  have hdisintegrate := S.coarse_substitution_observable p hpositive hless
    (fun actual cells => if actual = coarse then
      (if (R.clusterVertices actual root).card +
        ∑ edge, S.internalStateMass (R.rootChildState root actual edge) (cells edge) = size
       then (1 : ℝ) else 0) else 0)
  have hcollapse : (∑ actual : Configuration outerEdges,
      bernoulliWeight (S.reliability p) actual *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p (actual edge) (cells edge)) *
            (if actual = coarse then
              (if (R.clusterVertices actual root).card +
                ∑ edge, S.internalStateMass (R.rootChildState root actual edge) (cells edge) = size
               then (1 : ℝ) else 0) else 0)) =
      bernoulliWeight (S.reliability p) coarse *
        (∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
            if (R.clusterVertices coarse root).card +
              ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge) = size
            then 1 else 0) := by
    rw [Finset.sum_eq_single coarse]
    · simp
    · intro other _ hother
      simp [hother]
    · simp
  rw [hcollapse] at hdisintegrate
  rw [← hdisintegrate]
  unfold expectedBirthClusterCount
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [bernoulliWeight_substitutionConfiguration, Equiv.symm_apply_apply]
  apply Finset.sum_le_sum
  intro cells _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => bernoulliWeight_nonneg hp hp' _))
  by_cases hcoarse : S.coarseConfiguration cells = coarse
  · rw [if_pos hcoarse]
    have hbound := R.coarseRoot_atom_le_birthClusterCount S cells root (by rwa [hcoarse]) size
    rw [R.coarseRoot_cluster_mass S] at hbound
    exact_mod_cast hbound
  · rw [if_neg hcoarse]
    exact Nat.cast_nonneg _

end
end Universality.FiniteNetwork




