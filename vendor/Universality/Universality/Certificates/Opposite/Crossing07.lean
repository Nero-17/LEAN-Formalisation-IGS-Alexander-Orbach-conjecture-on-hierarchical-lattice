import Universality.Certificates.Opposite.Batch07
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows07Crossing : Fin 14 → ℕ := ![0,0,0,0,1,6,23,32,21,7,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows07_crossing : ∀ size : Fin 14,
    (oppositeRows07.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows07Crossing size := by
  decide

end Universality
