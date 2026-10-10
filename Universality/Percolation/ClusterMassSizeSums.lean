import Universality.Percolation.InternalClusterMassLimit
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem clusterFamily_size_count_mass (family : Finset (Finset (Fin vertices))) :
    (∑ size ∈ Finset.range (vertices + 1),
      size * (family.filter fun cluster => cluster.card = size).card) =
      ∑ cluster ∈ family, cluster.card := by
  classical
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cluster _
  have hcard : cluster.card < vertices + 1 := Nat.lt_succ_of_le (by simpa using Finset.card_le_univ cluster)
  simp [hcard, eq_comm]

theorem internalClusterCount_eq_zero (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (size : ℕ) (hsize : vertices < size) :
    R.internalClusterCount configuration size = 0 := by
  rw [R.internalClusterCount_eq_filter, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro cluster _ hcard
  have hle : cluster.card ≤ vertices := by simpa using Finset.card_le_univ cluster
  omega

theorem expectedInternalClusterCount_eq_zero (R : FiniteNetwork vertices edges)
    (p : ℝ) (size : ℕ) (hsize : vertices < size) : R.expectedInternalClusterCount p size = 0 := by
  simp only [expectedInternalClusterCount, R.internalClusterCount_eq_zero _ size hsize,
    Nat.cast_zero, mul_zero, Finset.sum_const_zero]

theorem sum_size_expectedInternalClusterCount (R : FiniteNetwork vertices edges) (p : ℝ) :
    (∑ size ∈ Finset.range (vertices + 1), (size : ℝ) * R.expectedInternalClusterCount p size) =
      R.expectedInternalClusterMass p := by
  unfold expectedInternalClusterCount expectedInternalClusterMass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  simp_rw [mul_left_comm (↑_ : ℝ) (bernoulliWeight p configuration)]
  rw [← Finset.mul_sum]
  congr 1
  have h := congrArg (fun value : ℕ => (value : ℝ))
    (clusterFamily_size_count_mass (R.internalClusterFamily configuration))
  push_cast at h
  simpa only [← R.internalClusterCount_eq_filter, internalClusterMass, Nat.cast_sum] using h

theorem hasSum_size_expectedInternalClusterCount (R : FiniteNetwork vertices edges) (p : ℝ) :
    HasSum (fun size : ℕ => (size : ℝ) * R.expectedInternalClusterCount p size)
      (R.expectedInternalClusterMass p) := by
  rw [← R.sum_size_expectedInternalClusterCount]
  apply hasSum_sum_of_ne_finset_zero
  intro size hsize
  have hlarge : vertices < size := by
    simp only [Finset.mem_range] at hsize
    omega
  rw [R.expectedInternalClusterCount_eq_zero p size hlarge, mul_zero]

theorem birthClusterCount_eq_zero (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges)
    (size : ℕ) (hsize : Fintype.card (R.SubstitutionVertex S) < size) :
    R.birthClusterCount S configuration size = 0 := by
  unfold birthClusterCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro cluster _ hcard
  have hle : cluster.card ≤ Fintype.card (R.SubstitutionVertex S) := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ cluster
  omega

theorem expectedBirthClusterCount_eq_zero (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ)
    (size : ℕ) (hsize : Fintype.card (R.SubstitutionVertex S) < size) :
    R.expectedBirthClusterCount S p size = 0 := by
  simp only [expectedBirthClusterCount, R.birthClusterCount_eq_zero S _ size hsize,
    Nat.cast_zero, mul_zero, Finset.sum_const_zero]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem expectedClusterBirth_size_summable (rule : Rule) (p : ℝ) (n : ℕ) :
    Summable (fun size : ℕ => (size : ℝ) * rule.expectedClusterBirth p size n) := by
  cases n with
  | zero => exact (rule.network.hasSum_size_expectedInternalClusterCount p).summable
  | succ n =>
    apply summable_of_ne_finset_zero (s := Finset.range (Fintype.card
      (rule.network.SubstitutionVertex (rule.generation n).network) + 1))
    intro size hsize
    have hlarge : Fintype.card (rule.network.SubstitutionVertex (rule.generation n).network) < size := by
      simp only [Finset.mem_range] at hsize
      omega
    change (size : ℝ) * rule.network.expectedBirthClusterCount _ p size = 0
    rw [rule.network.expectedBirthClusterCount_eq_zero _ p size hlarge, mul_zero]

end
end Universality.Rule
