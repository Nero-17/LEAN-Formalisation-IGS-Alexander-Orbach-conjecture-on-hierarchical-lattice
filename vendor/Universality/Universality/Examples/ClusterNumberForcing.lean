import Universality.Examples.ClusterNumberCounts

namespace Universality
noncomputable section
open FiniteNetwork Polynomial
set_option maxHeartbeats 0
theorem diamond_internalClusterPolynomial :
    diamondNetwork.internalClusterPolynomial = 2 * (1 - X) ^ 2 := by
  rw [internalClusterPolynomial_bernstein]
  have h0 : diamondNetwork.internalClusterCountByOpenSize 0 = 2 := diamond_internal_cluster_counts 0
  have h1 : diamondNetwork.internalClusterCountByOpenSize 1 = 4 := diamond_internal_cluster_counts 1
  have h2 : diamondNetwork.internalClusterCountByOpenSize 2 = 2 := diamond_internal_cluster_counts 2
  have h3 : diamondNetwork.internalClusterCountByOpenSize 3 = 0 := diamond_internal_cluster_counts 3
  have h4 : diamondNetwork.internalClusterCountByOpenSize 4 = 0 := diamond_internal_cluster_counts 4
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3, h4]
  norm_num
  ring

theorem wheatstone_internalClusterPolynomial :
    wheatstoneNetwork.internalClusterPolynomial =
      2 - 5 * X + 2 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 + X ^ 5 := by
  rw [internalClusterPolynomial_bernstein]
  have h0 : wheatstoneNetwork.internalClusterCountByOpenSize 0 = 2 := wheatstone_internal_cluster_counts 0
  have h1 : wheatstoneNetwork.internalClusterCountByOpenSize 1 = 5 := wheatstone_internal_cluster_counts 1
  have h2 : wheatstoneNetwork.internalClusterCountByOpenSize 2 = 2 := wheatstone_internal_cluster_counts 2
  have h3 : wheatstoneNetwork.internalClusterCountByOpenSize 3 = 0 := wheatstone_internal_cluster_counts 3
  have h4 : wheatstoneNetwork.internalClusterCountByOpenSize 4 = 0 := wheatstone_internal_cluster_counts 4
  have h5 : wheatstoneNetwork.internalClusterCountByOpenSize 5 = 0 := wheatstone_internal_cluster_counts 5
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3, h4, h5]
  norm_num
  ring

theorem diamond_expectedInternalClusterNumber (p : ℝ) :
    diamondNetwork.expectedInternalClusterNumber p = 2 * (1 - p) ^ 2 := by
  rw [← diamondNetwork.internalClusterPolynomial_eval, diamond_internalClusterPolynomial]
  simp [Polynomial.eval₂_pow]

theorem wheatstone_expectedInternalClusterNumber (p : ℝ) :
    wheatstoneNetwork.expectedInternalClusterNumber p =
      2 - 5 * p + 2 * p ^ 2 + 4 * p ^ 3 - 4 * p ^ 4 + p ^ 5 := by
  rw [← wheatstoneNetwork.internalClusterPolynomial_eval, wheatstone_internalClusterPolynomial]
  simp [Polynomial.eval₂_pow]

end
end Universality
