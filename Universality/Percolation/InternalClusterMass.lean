import Universality.Percolation.ClusterSizeDensity
import Universality.Percolation.BoundaryMassDensity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem selectedActive_both_iff (configuration : Configuration edges) (root : Fin vertices) :
    R.selectedActive true true configuration root = true ↔
      R.source ∈ R.clusterVertices configuration root ∨ R.target ∈ R.clusterVertices configuration root := by
  simp only [selectedActive, Bool.true_and, Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true,
    R.mem_clusterVertices]
  exact or_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
    ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

theorem sum_selectedActive_both (configuration : Configuration edges) :
    (∑ root : Fin vertices, if R.selectedActive true true configuration root then (1 : ℕ) else 0) =
      R.internalSelectedMass true true configuration + 2 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin vertices)))
    (p := fun root => root ≠ R.source ∧ root ≠ R.target)
    (f := fun root => if R.selectedActive true true configuration root then (1 : ℕ) else 0)
  have hinterior : (∑ root ∈ Finset.univ.filter (fun root => root ≠ R.source ∧ root ≠ R.target),
      if R.selectedActive true true configuration root then (1 : ℕ) else 0) =
      R.internalSelectedMass true true configuration := by
    exact Finset.sum_subtype _ (by simp) _
  have hterminals : (Finset.univ.filter fun root : Fin vertices => ¬ (root ≠ R.source ∧ root ≠ R.target)) =
      {R.source, R.target} := by
    ext root
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not,
      Finset.mem_insert, Finset.mem_singleton]
  have hs : R.selectedActive true true configuration R.source = true :=
    (R.selectedActive_both_iff _ _).mpr (Or.inl (R.root_mem_clusterVertices _ _))
  have ht : R.selectedActive true true configuration R.target = true :=
    (R.selectedActive_both_iff _ _).mpr (Or.inr (R.root_mem_clusterVertices _ _))
  rw [hinterior, hterminals] at hsplit
  simp only [Finset.sum_pair R.terminals_distinct, hs, ht, ↓reduceIte] at hsplit
  exact hsplit.symm

def internalClusterMass (configuration : Configuration edges) : ℕ :=
  ∑ cluster ∈ R.internalClusterFamily configuration, cluster.card

theorem internalClusterMass_partition (configuration : Configuration edges) :
    (R.internalClusterMass configuration : ℝ) + R.internalSelectedMass true true configuration + 2 = vertices := by
  have hmass := R.sum_roots_eq_sum_clusters configuration
    (fun cluster => if R.source ∉ cluster ∧ R.target ∉ cluster then 1 else 0)
  have hclusters : (∑ cluster ∈ R.clusterFamily configuration,
      (cluster.card : ℝ) * (if R.source ∉ cluster ∧ R.target ∉ cluster then 1 else 0)) =
      R.internalClusterMass configuration := by
    simp only [internalClusterMass, internalClusterFamily, Nat.cast_sum, Finset.sum_filter,
      mul_ite, mul_one, mul_zero, Nat.cast_ite, Nat.cast_zero]
  rw [hclusters] at hmass
  have htotal : (∑ root : Fin vertices,
      ((if R.source ∉ R.clusterVertices configuration root ∧ R.target ∉ R.clusterVertices configuration root
        then (1 : ℝ) else 0) +
      (if R.selectedActive true true configuration root then (1 : ℝ) else 0))) = vertices := by
    trans ∑ _ : Fin vertices, (1 : ℝ)
    · apply Finset.sum_congr rfl
      intro root _
      have h := R.selectedActive_both_iff configuration root
      by_cases hactive : R.selectedActive true true configuration root = true
      · have hor := h.mp hactive
        simp only [hactive, ↓reduceIte]
        rcases hor with hs | ht
        · simp [hs]
        · simp [ht]
      · have hneither := mt h.mpr hactive
        simp only [not_or] at hneither
        simp [hactive, hneither.1, hneither.2]
    · simp
  rw [Finset.sum_add_distrib, hmass] at htotal
  have hselected := congrArg (fun value : ℕ => (value : ℝ)) (R.sum_selectedActive_both configuration)
  push_cast at hselected
  rw [hselected] at htotal
  linarith

end
end Universality.FiniteNetwork
