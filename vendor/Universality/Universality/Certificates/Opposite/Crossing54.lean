import Universality.Certificates.Opposite.Batch54
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows54Crossing : Fin 14 → ℕ := ![0,0,0,0,0,1,6,19,30,21,7,1,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows54_crossing : ∀ size : Fin 14,
    (oppositeRows54.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows54Crossing size := by
  decide

end Universality
