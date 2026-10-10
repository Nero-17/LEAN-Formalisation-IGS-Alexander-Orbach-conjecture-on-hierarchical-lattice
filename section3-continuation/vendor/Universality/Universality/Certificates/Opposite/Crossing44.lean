import Universality.Certificates.Opposite.Batch44
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows44Crossing : Fin 14 → ℕ := ![0,0,0,0,1,6,19,30,21,7,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows44_crossing : ∀ size : Fin 14,
    (oppositeRows44.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows44Crossing size := by
  decide

end Universality
