import Universality.Certificates.Opposite.Batch51
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows51Crossing : Fin 14 → ℕ := ![0,0,0,0,0,1,6,23,32,21,7,1,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows51_crossing : ∀ size : Fin 14,
    (oppositeRows51.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows51Crossing size := by
  decide

end Universality
