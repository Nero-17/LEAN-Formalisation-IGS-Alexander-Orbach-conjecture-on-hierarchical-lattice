import Universality.Percolation.Wheatstone
import Universality.Percolation.ConfigurationEncoding

namespace Universality
open FiniteNetwork

/-- The thirteen-edge network obtained by replacing the opposite outer edges
source-upper and lower-target of the Wheatstone skeleton by Wheatstone cells. -/
def oppositeWheatstoneNetwork : FiniteNetwork 8 13 where
  endpoint := ![(2, 1), (0, 3), (2, 3),
    (0, 4), (4, 2), (0, 5), (5, 2), (4, 5),
    (3, 6), (6, 1), (3, 7), (7, 1), (6, 7)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

end Universality
