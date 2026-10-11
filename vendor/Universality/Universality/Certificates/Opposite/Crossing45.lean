import Universality.Certificates.Opposite.Batch45
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows45Crossing : Fin 14 → ℕ := ![0,0,0,0,0,1,6,23,32,21,7,1,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows45_crossing : ∀ size : Fin 14,
    (oppositeRows45.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows45Crossing size := by
  decide

end Universality
