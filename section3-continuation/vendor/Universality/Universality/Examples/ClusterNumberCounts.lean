import Universality.Examples.ClusterCountCertificates

namespace Universality
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open FiniteNetwork Polynomial

theorem diamond_internal_cluster_counts :
    ∀ k : Fin 5, diamondNetwork.internalClusterCountByOpenSize k = ![2, 4, 2, 0, 0] k := by
  have hcounts : ∀ k : Fin 5,
      (diamondClusterRows.map fun row => if openCount row.configuration = k.val then
        row.internalCount diamondNetwork else 0).sum = ![2, 4, 2, 0, 0] k := by decide +kernel
  intro k
  rw [← diamondNetwork.certified_internalClusterCountByOpenSize diamondClusterRows
    diamondClusterRows_indices diamondClusterRows_valid]
  exact hcounts k

theorem wheatstone_internal_cluster_counts :
    ∀ k : Fin 6, wheatstoneNetwork.internalClusterCountByOpenSize k = ![2, 5, 2, 0, 0, 0] k := by
  have hcounts : ∀ k : Fin 6,
      (wheatstoneClusterRows.map fun row => if openCount row.configuration = k.val then
        row.internalCount wheatstoneNetwork else 0).sum = ![2, 5, 2, 0, 0, 0] k := by decide +kernel
  intro k
  rw [← wheatstoneNetwork.certified_internalClusterCountByOpenSize wheatstoneClusterRows
    wheatstoneClusterRows_indices wheatstoneClusterRows_valid]
  exact hcounts k

end
end Universality
