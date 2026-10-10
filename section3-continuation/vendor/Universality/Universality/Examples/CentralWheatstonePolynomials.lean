import Universality.Examples.CentralWheatstoneCounts
import Universality.Percolation.ReliabilityDerivative

namespace Universality
noncomputable section
open FiniteNetwork Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centralWheatstone_reliabilityPolynomial :
    centralWheatstoneNetwork.reliabilityPolynomial =
      2 * X ^ 2 + 3 * X ^ 4 - 4 * X ^ 5 - 14 * X ^ 6 + 28 * X ^ 7 - 18 * X ^ 8 + 4 * X ^ 9 := by
  rw [reliabilityPolynomial_bernstein]
  have h0 : centralWheatstoneNetwork.crossingCountBySize 0 = 0 := centralWheatstone_crossing_counts 0
  have h1 : centralWheatstoneNetwork.crossingCountBySize 1 = 0 := centralWheatstone_crossing_counts 1
  have h2 : centralWheatstoneNetwork.crossingCountBySize 2 = 2 := centralWheatstone_crossing_counts 2
  have h3 : centralWheatstoneNetwork.crossingCountBySize 3 = 14 := centralWheatstone_crossing_counts 3
  have h4 : centralWheatstoneNetwork.crossingCountBySize 4 = 45 := centralWheatstone_crossing_counts 4
  have h5 : centralWheatstoneNetwork.crossingCountBySize 5 = 81 := centralWheatstone_crossing_counts 5
  have h6 : centralWheatstoneNetwork.crossingCountBySize 6 = 70 := centralWheatstone_crossing_counts 6
  have h7 : centralWheatstoneNetwork.crossingCountBySize 7 = 34 := centralWheatstone_crossing_counts 7
  have h8 : centralWheatstoneNetwork.crossingCountBySize 8 = 9 := centralWheatstone_crossing_counts 8
  have h9 : centralWheatstoneNetwork.crossingCountBySize 9 = 1 := centralWheatstone_crossing_counts 9
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  ring

theorem centralWheatstone_internalClusterPolynomial :
    centralWheatstoneNetwork.internalClusterPolynomial =
      4 - 9 * X + 2 * X ^ 2 + 2 * X ^ 3 + 9 * X ^ 4 - X ^ 5 -
        26 * X ^ 6 + 30 * X ^ 7 - 13 * X ^ 8 + 2 * X ^ 9 := by
  rw [internalClusterPolynomial_bernstein]
  have h0 : centralWheatstoneNetwork.internalClusterCountByOpenSize 0 = 4 := centralWheatstone_internal_cluster_counts 0
  have h1 : centralWheatstoneNetwork.internalClusterCountByOpenSize 1 = 27 := centralWheatstone_internal_cluster_counts 1
  have h2 : centralWheatstoneNetwork.internalClusterCountByOpenSize 2 = 74 := centralWheatstone_internal_cluster_counts 2
  have h3 : centralWheatstoneNetwork.internalClusterCountByOpenSize 3 = 100 := centralWheatstone_internal_cluster_counts 3
  have h4 : centralWheatstoneNetwork.internalClusterCountByOpenSize 4 = 63 := centralWheatstone_internal_cluster_counts 4
  have h5 : centralWheatstoneNetwork.internalClusterCountByOpenSize 5 = 18 := centralWheatstone_internal_cluster_counts 5
  have h6 : centralWheatstoneNetwork.internalClusterCountByOpenSize 6 = 2 := centralWheatstone_internal_cluster_counts 6
  have h7 : centralWheatstoneNetwork.internalClusterCountByOpenSize 7 = 0 := centralWheatstone_internal_cluster_counts 7
  have h8 : centralWheatstoneNetwork.internalClusterCountByOpenSize 8 = 0 := centralWheatstone_internal_cluster_counts 8
  have h9 : centralWheatstoneNetwork.internalClusterCountByOpenSize 9 = 0 := centralWheatstone_internal_cluster_counts 9
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num
  ring

theorem centralWheatstone_reliability (p : ℝ) :
    centralWheatstoneNetwork.reliability p =
      2 * p ^ 2 + 3 * p ^ 4 - 4 * p ^ 5 - 14 * p ^ 6 + 28 * p ^ 7 - 18 * p ^ 8 + 4 * p ^ 9 := by
  rw [← centralWheatstoneNetwork.reliabilityPolynomial_eval, centralWheatstone_reliabilityPolynomial]
  simp

theorem centralWheatstone_expectedInternalClusterNumber (p : ℝ) :
    centralWheatstoneNetwork.expectedInternalClusterNumber p =
      4 - 9 * p + 2 * p ^ 2 + 2 * p ^ 3 + 9 * p ^ 4 - p ^ 5 -
        26 * p ^ 6 + 30 * p ^ 7 - 13 * p ^ 8 + 2 * p ^ 9 := by
  rw [← centralWheatstoneNetwork.internalClusterPolynomial_eval, centralWheatstone_internalClusterPolynomial]
  simp

theorem centralWheatstone_critical_fixed_point : centralWheatstoneNetwork.reliability (1 / 2) = 1 / 2 := by
  rw [centralWheatstone_reliability]
  norm_num

end
end Universality
