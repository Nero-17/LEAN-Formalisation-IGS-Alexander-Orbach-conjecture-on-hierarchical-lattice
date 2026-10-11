import Universality.Percolation.CertifiedClusterCounts
import Universality.Percolation.CertifiedReliability

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)

def FullComponentRow.toComponentRow (row : FullComponentRow vertices edges) : ComponentRow vertices edges :=
  ⟨row.index, row.component network.source, row.component network.target⟩

theorem certified_full_crossingCountBySize
    (rows : List (FullComponentRow vertices edges))
    (indices : rows.map FullComponentRow.index = List.finRange (2 ^ edges))
    (valid : ∀ row ∈ rows, row.Valid network) (size : ℕ) :
    (rows.map fun row => (row.toComponentRow network).crossingBySize network size).sum =
      network.crossingCountBySize size := by
  have hindices : (rows.map (FullComponentRow.toComponentRow network)).map ComponentRow.index =
      List.finRange (2 ^ edges) := by
    simpa only [List.map_map, Function.comp_def, FullComponentRow.toComponentRow] using indices
  have hvalid : ∀ row ∈ rows.map (FullComponentRow.toComponentRow network), row.Valid network := by
    intro row hrow
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrow
    exact ⟨valid original horiginal network.source, valid original horiginal network.target⟩
  simpa only [List.map_map, Function.comp_def] using
    network.certified_crossingCountBySize _ hindices hvalid size

end Universality.FiniteNetwork
