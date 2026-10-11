import Universality.Certificates.Opposite.Batch47
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows47Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,1,6,23,32,21,7,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows47_crossing : ∀ size : Fin 14,
    (oppositeRows47.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows47Crossing size := by
  decide

end Universality
