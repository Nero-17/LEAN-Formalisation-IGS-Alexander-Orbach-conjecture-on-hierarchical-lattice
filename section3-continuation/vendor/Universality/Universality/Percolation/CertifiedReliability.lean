import Universality.Percolation.CertifiedCounts
import Universality.Percolation.ReliabilityPolynomial

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def ComponentRow.crossingBySize (row : ComponentRow vertices edges) (size : ℕ) : ℕ :=
  if row.condition R .connected && decide (openCount row.configuration = size) then 1 else 0

theorem certified_crossingCountBySize
    (rows : List (ComponentRow vertices edges))
    (indices : rows.map ComponentRow.index = List.finRange (2 ^ edges))
    (valid : ∀ row ∈ rows, row.Valid R) (size : ℕ) :
    (rows.map fun row => row.crossingBySize R size).sum = R.crossingCountBySize size := by
  rw [crossingCountBySize, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply sum_component_rows rows indices
  intro row hrow
  simp only [ComponentRow.crossingBySize, row.condition_eq R (valid row hrow),
    conditioning, Bool.and_eq_true, decide_eq_true_eq]

end Universality.FiniteNetwork
