import Universality.Certificates.Opposite.Batch01
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows01Crossing : Fin 14 → ℕ := ![0,0,0,0,5,16,15,6,1,0,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows01_crossing : ∀ size : Fin 14,
    (oppositeRows01.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows01Crossing size := by
  decide

end Universality
