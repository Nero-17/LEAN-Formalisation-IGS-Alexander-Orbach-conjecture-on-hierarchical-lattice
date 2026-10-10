import Universality.Certificates.Opposite.Batch62
import Universality.Percolation.CertifiedReliability

namespace Universality
open FiniteNetwork

def oppositeRows62Crossing : Fin 14 → ℕ := ![0,0,0,0,0,0,1,6,19,30,21,7,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem oppositeRows62_crossing : ∀ size : Fin 14,
    (oppositeRows62.map fun row => row.crossingBySize oppositeWheatstoneNetwork size.val).sum =
      oppositeRows62Crossing size := by
  decide

end Universality
