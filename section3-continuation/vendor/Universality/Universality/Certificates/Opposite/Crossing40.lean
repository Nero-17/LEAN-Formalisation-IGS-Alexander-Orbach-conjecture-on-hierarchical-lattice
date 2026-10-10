import Universality.Certificates.Opposite.Batch40
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows40Crossing : Fin 14 → ℕ := ![0,0,0,0,0,3,12,15,6,1,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows40_crossing : ∀ size : Fin 14,
    (oppositeRows40.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows40Crossing size := by
  decide

end Universality
