import Universality.Certificates.Opposite.Batch58
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows58Crossing : Fin 14 → ℕ := ![0,0,0,0,0,1,6,19,30,21,7,1,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows58_crossing : ∀ size : Fin 14,
    (oppositeRows58.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows58Crossing size := by
  decide

end Universality
