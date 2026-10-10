import Universality.Certificates.Opposite.Batch08
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows08Crossing : Fin 14 → ℕ := ![0,0,0,0,3,12,15,6,1,0,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows08_crossing : ∀ size : Fin 14,
    (oppositeRows08.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows08Crossing size := by
  decide

end Universality
