import Universality.Certificates.Opposite.Batch11
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows11Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,5,16,15,6,1,0,0,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows11_crossing : ∀ size : Fin 14,
    (oppositeRows11.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows11Crossing size := by
  decide

end Universality
