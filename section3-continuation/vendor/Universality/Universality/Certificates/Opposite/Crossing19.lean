import Universality.Certificates.Opposite.Batch19
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows19Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,5,16,15,6,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows19_crossing : ∀ size : Fin 14,
    (oppositeRows19.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows19Crossing size := by
  decide

end Universality
