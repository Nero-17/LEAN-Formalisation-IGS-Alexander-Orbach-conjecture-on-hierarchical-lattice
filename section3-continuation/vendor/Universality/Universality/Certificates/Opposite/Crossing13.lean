import Universality.Certificates.Opposite.Batch13
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows13Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,5,16,15,6,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows13_crossing : ∀ size : Fin 14,
    (oppositeRows13.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows13Crossing size := by
  decide

end Universality
