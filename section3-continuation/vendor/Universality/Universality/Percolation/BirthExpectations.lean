import Universality.Percolation.BirthClusters
import Universality.Percolation.ClusterEquivalence
import Universality.Percolation.ClusterNumberSeries
import Universality.Graph.GenerationReassociation

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def expectedInternalClusterCount (R : FiniteNetwork vertices edges) (p : ℝ) (size : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalClusterCount configuration size

def expectedBirthClusterCount (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) (size : ℕ) : ℝ :=
  ∑ configuration : Configuration (outerEdges * innerEdges),
    bernoulliWeight p configuration *
      R.birthClusterCount S (substitutionConfigurationEquiv.symm configuration) size

theorem expectedInternalClusterCount_bounds (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ R.expectedInternalClusterCount p size ∧ R.expectedInternalClusterCount p size ≤ vertices := by
  constructor
  · exact Finset.sum_nonneg (fun configuration _ =>
      mul_nonneg (bernoulliWeight_nonneg hp hp' _) (Nat.cast_nonneg _))
  · calc
      _ ≤ ∑ configuration : Configuration edges, bernoulliWeight p configuration * (vertices : ℝ) := by
        apply Finset.sum_le_sum
        intro configuration _
        apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
        have h := (Finset.card_filter_le (R.internalClusterFamily configuration)
          (fun cluster => cluster.card = size)).trans (R.internalClusterFamily_card_le configuration)
        rw [← R.internalClusterCount_eq_filter] at h
        exact_mod_cast h
      _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem expectedBirthClusterCount_bounds (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ R.expectedBirthClusterCount S p size ∧ R.expectedBirthClusterCount S p size ≤ outerVertices := by
  constructor
  · exact Finset.sum_nonneg (fun configuration _ =>
      mul_nonneg (bernoulliWeight_nonneg hp hp' _) (Nat.cast_nonneg _))
  · calc
      _ ≤ ∑ configuration : Configuration (outerEdges * innerEdges),
          bernoulliWeight p configuration * (outerVertices : ℝ) := by
        apply Finset.sum_le_sum
        intro configuration _
        apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
        exact_mod_cast R.birthClusterCount_le_vertices S (substitutionConfigurationEquiv.symm configuration) size
      _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem expectedInternalClusterCount_substitute (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) (size : ℕ) :
    (R.substitute S).expectedInternalClusterCount p size =
      (outerEdges : ℝ) * S.expectedInternalClusterCount p size + R.expectedBirthClusterCount S p size := by
  unfold expectedInternalClusterCount expectedBirthClusterCount
  rw [← substitutionConfigurationEquiv.sum_comp]
  conv_rhs => rhs; rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalClusterCount_substitute S, Equiv.symm_apply_apply,
    bernoulliWeight_substitutionConfiguration, Nat.cast_add, Nat.cast_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) * (S.internalClusterCount (configuration edge) size : ℝ)) =
      ∑ configuration, bernoulliWeight p configuration * (S.internalClusterCount configuration size : ℝ) := by
    rw [Universality.finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => (S.internalClusterCount cell size : ℝ)) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul]
  simp_rw [hlocal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem NetworkEquivalence.expectedInternalClusterCount
    {R : FiniteNetwork outerVertices outerEdges} {S : FiniteNetwork innerVertices innerEdges}
    (equivalence : R.NetworkEquivalence S) (p : ℝ) (size : ℕ) :
    S.expectedInternalClusterCount p size = R.expectedInternalClusterCount p size := by
  unfold FiniteNetwork.expectedInternalClusterCount
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.bernoulliWeight, equivalence.internalClusterCount]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem generation_expectedInternalClusterCount (rule : Rule) (n : ℕ) (p : ℝ) (size : ℕ) :
    (rule.generation (n + 1)).network.expectedInternalClusterCount p size =
      (rule.edges : ℝ) * (rule.generation n).network.expectedInternalClusterCount p size +
        rule.network.expectedBirthClusterCount (rule.generation n).network p size := by
  rw [← (rule.generationTopDecomposition n).expectedInternalClusterCount,
    FiniteNetwork.expectedInternalClusterCount_substitute]

end
end Universality.Rule
