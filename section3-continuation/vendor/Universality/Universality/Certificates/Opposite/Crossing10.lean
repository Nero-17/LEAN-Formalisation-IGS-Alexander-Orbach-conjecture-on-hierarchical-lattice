import Universality.Certificates.Opposite.Batch10
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows10Crossing : Fin 14 → ℕ := ![0,0,0,0,0,3,12,15,6,1,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows10_crossing : ∀ size : Fin 14,
    (oppositeRows10.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows10Crossing size := by
  decide

end Universality
