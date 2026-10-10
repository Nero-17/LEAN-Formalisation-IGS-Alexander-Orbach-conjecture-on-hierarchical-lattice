import Universality.Certificates.Opposite.Batch16
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows16Crossing : Fin 14 → ℕ := ![0,0,0,0,3,12,15,6,1,0,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows16_crossing : ∀ size : Fin 14,
    (oppositeRows16.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows16Crossing size := by
  decide

end Universality
