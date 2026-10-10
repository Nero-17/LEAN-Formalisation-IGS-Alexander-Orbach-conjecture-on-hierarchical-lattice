import Universality.Certificates.Opposite.Batch37
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows37Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,5,16,15,6,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows37_crossing : ∀ size : Fin 14,
    (oppositeRows37.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows37Crossing size := by
  decide

end Universality
