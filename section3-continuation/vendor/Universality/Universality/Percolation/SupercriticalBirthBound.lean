import Universality.Percolation.AnnealedBirthMomentLower

namespace Universality.FiniteNetwork
noncomputable section
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem birthClusterFamily_eq_empty_of_all_cross
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (hcross : ∀ edge, S.crosses (configuration edge) = true) :
    R.birthClusterFamily S configuration = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro cluster hcluster
  obtain ⟨hinternal, htouch⟩ := Finset.mem_filter.mp hcluster
  obtain ⟨hfamily, hsource, htarget⟩ := Finset.mem_filter.mp hinternal
  obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp htouch
  obtain ⟨old, _, rfl⟩ := Finset.mem_image.mp hcoarse
  have hcoarseConfiguration : S.coarseConfiguration configuration = fun _ => true := by
    funext edge
    exact hcross edge
  have hreach : ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (Fintype.equivFin _ (Sum.inl old)) (R.substitute S).source := by
    change ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (Fintype.equivFin _ (Sum.inl old)) (Fintype.equivFin _ (Sum.inl R.source))
    rw [R.substitute_reachable_iff S configuration, R.substitutedReachable_iff S configuration,
      hcoarseConfiguration]
    exact (hconnected old).symm
  apply hsource
  rw [← (R.substitute S).clusterVertices_eq_of_mem _ cluster hfamily _ hvertex]
  exact ((R.substitute S).mem_clusterVertices _ _ _).mpr hreach

theorem birthClusterPower_le_failure_count
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges) (order : ℕ) :
    (∑ cluster ∈ R.birthClusterFamily S configuration, (cluster.card : ℝ) ^ order) ≤
      (outerVertices : ℝ) * (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order *
        ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (0 : ℝ) else 1 := by
  by_cases hall : ∀ edge, S.crosses (configuration edge) = true
  · simp only [R.birthClusterFamily_eq_empty_of_all_cross S hconnected configuration hall, Finset.sum_empty]
    positivity
  · push Not at hall
    obtain ⟨edge, hedge⟩ := hall
    have hsum : (1 : ℝ) ≤ ∑ e : Fin outerEdges, if S.crosses (configuration e) then (0 : ℝ) else 1 := by
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun e : Fin outerEdges => if S.crosses (configuration e) then (0 : ℝ) else 1)
        (fun e _ => by split <;> norm_num) (Finset.mem_univ edge)
      simpa only [hedge, Bool.false_eq_true, ↓reduceIte] using hs
    calc
      _ ≤ ∑ _cluster ∈ R.birthClusterFamily S configuration,
          (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order := by
        apply Finset.sum_le_sum
        intro cluster _
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast (show cluster.card ≤ Fintype.card (R.SubstitutionVertex S) by
          simpa only [Fintype.card_fin] using Finset.card_le_univ cluster)
      _ = ((R.birthClusterFamily S configuration).card : ℝ) *
          (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order := by simp
      _ ≤ (outerVertices : ℝ) * (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast R.birthClusterFamily_card_le_vertices S configuration)
          (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hsum

theorem expectedBirthClusterPower_le_failure
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    R.expectedBirthClusterPower S p order ≤
      (outerVertices : ℝ) * (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order *
        ((outerEdges : ℝ) * (1 - S.reliability p)) := by
  have hlocal : (∑ configuration : Configuration innerEdges, bernoulliWeight p configuration *
      (if S.crosses configuration then (0 : ℝ) else 1)) = 1 - S.reliability p := by
    calc
      _ = ∑ configuration : Configuration innerEdges,
          (bernoulliWeight p configuration -
            if S.crosses configuration then bernoulliWeight p configuration else 0) := by
        apply Finset.sum_congr rfl
        intro configuration _
        split <;> simp_all
      _ = _ := by rw [Finset.sum_sub_distrib, sum_bernoulliWeight]; rfl
  have hfailure : (∑ configuration : Fin outerEdges → Configuration innerEdges,
      (∏ edge, bernoulliWeight p (configuration edge)) *
        ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (0 : ℝ) else 1) =
      (outerEdges : ℝ) * (1 - S.reliability p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hedge (edge : Fin outerEdges) :
        (∑ configuration : Fin outerEdges → Configuration innerEdges,
          (∏ e, bernoulliWeight p (configuration e)) *
            (if S.crosses (configuration edge) then (0 : ℝ) else 1)) = 1 - S.reliability p := by
      rw [finite_product_local_moment
        (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
        (fun cell => if S.crosses cell then (0 : ℝ) else 1) edge]
      simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul, hlocal]
    simp only [hedge, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold expectedBirthClusterPower
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, bernoulliWeight_substitutionConfiguration]
  calc
    _ ≤ ∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ edge, bernoulliWeight p (configuration edge)) *
          ((outerVertices : ℝ) * (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order *
            ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (0 : ℝ) else 1) := by
      apply Finset.sum_le_sum
      intro configuration _
      exact mul_le_mul_of_nonneg_left (R.birthClusterPower_le_failure_count S hconnected configuration order)
        (Finset.prod_nonneg (fun edge _ => bernoulliWeight_nonneg hp hp' _))
    _ = _ := by
      simp_rw [mul_left_comm _
        ((outerVertices : ℝ) * (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order)]
      rw [← Finset.mul_sum, hfailure]

end
end Universality.FiniteNetwork
