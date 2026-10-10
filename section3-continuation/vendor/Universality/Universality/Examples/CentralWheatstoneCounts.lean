import Universality.Examples.CentralWheatstoneCertificates.Batch00
import Universality.Examples.CentralWheatstoneCertificates.Batch01
import Universality.Examples.CentralWheatstoneCertificates.Batch02
import Universality.Examples.CentralWheatstoneCertificates.Batch03
import Universality.Examples.CentralWheatstoneCertificates.Batch04
import Universality.Examples.CentralWheatstoneCertificates.Batch05
import Universality.Examples.CentralWheatstoneCertificates.Batch06
import Universality.Examples.CentralWheatstoneCertificates.Batch07

namespace Universality
open FiniteNetwork
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def centralWheatstoneClusterRows : List (FullComponentRow 6 9) :=
  centralWheatstoneRows00 ++
  centralWheatstoneRows01 ++
  centralWheatstoneRows02 ++
  centralWheatstoneRows03 ++
  centralWheatstoneRows04 ++
  centralWheatstoneRows05 ++
  centralWheatstoneRows06 ++
  centralWheatstoneRows07

theorem centralWheatstoneClusterRows_indices :
    centralWheatstoneClusterRows.map FullComponentRow.index = List.finRange (2 ^ 9) := by
  decide +kernel

theorem centralWheatstoneClusterRows_valid :
    ∀ row ∈ centralWheatstoneClusterRows, row.Valid centralWheatstoneNetwork := by
  have h : centralWheatstoneClusterRows.all (fun row => decide (row.Valid centralWheatstoneNetwork)) = true := by
    simp only [centralWheatstoneClusterRows, List.all_append, centralWheatstoneRows00_valid, centralWheatstoneRows01_valid, centralWheatstoneRows02_valid, centralWheatstoneRows03_valid, centralWheatstoneRows04_valid, centralWheatstoneRows05_valid, centralWheatstoneRows06_valid, centralWheatstoneRows07_valid]
    rfl
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem centralWheatstone_crossing_counts (size : Fin 10) :
    centralWheatstoneNetwork.crossingCountBySize size = ![0, 0, 2, 14, 45, 81, 70, 34, 9, 1] size := by
  rw [← certified_full_crossingCountBySize centralWheatstoneNetwork centralWheatstoneClusterRows
    centralWheatstoneClusterRows_indices centralWheatstoneClusterRows_valid]
  simp only [centralWheatstoneClusterRows, List.map_append, List.sum_append, centralWheatstoneRows00_crossing, centralWheatstoneRows01_crossing, centralWheatstoneRows02_crossing, centralWheatstoneRows03_crossing, centralWheatstoneRows04_crossing, centralWheatstoneRows05_crossing, centralWheatstoneRows06_crossing, centralWheatstoneRows07_crossing]
  fin_cases size <;> rfl

theorem centralWheatstone_internal_cluster_counts (size : Fin 10) :
    centralWheatstoneNetwork.internalClusterCountByOpenSize size = ![4, 27, 74, 100, 63, 18, 2, 0, 0, 0] size := by
  rw [← certified_internalClusterCountByOpenSize centralWheatstoneNetwork centralWheatstoneClusterRows
    centralWheatstoneClusterRows_indices centralWheatstoneClusterRows_valid]
  simp only [centralWheatstoneClusterRows, List.map_append, List.sum_append, centralWheatstoneRows00_internal, centralWheatstoneRows01_internal, centralWheatstoneRows02_internal, centralWheatstoneRows03_internal, centralWheatstoneRows04_internal, centralWheatstoneRows05_internal, centralWheatstoneRows06_internal, centralWheatstoneRows07_internal]
  fin_cases size <;> rfl

end Universality
