import Universality.Certificates.Opposite.Batch48
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows48Crossing : Fin 14 → ℕ := ![0,0,0,0,0,3,12,15,6,1,0,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows48_crossing : ∀ size : Fin 14,
    (oppositeRows48.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows48Crossing size := by
  decide

end Universality
