import Universality.Percolation.TerminalSymmetry
import Universality.Percolation.OppositeWheatstone

namespace Universality
open FiniteNetwork

def oppositeWheatstoneTerminalSymmetry : oppositeWheatstoneNetwork.NetworkSymmetry where
  vertex := (((Equiv.swap 0 1).trans (Equiv.swap 2 3)).trans (Equiv.swap 4 6)).trans (Equiv.swap 5 7)
  edge := (((((Equiv.swap 0 1).trans (Equiv.swap 3 9)).trans
    (Equiv.swap 4 8)).trans (Equiv.swap 5 11)).trans (Equiv.swap 6 10)).trans (Equiv.swap 7 12)
  endpoint := by decide

theorem oppositeWheatstone_terminal_symmetry_source :
    oppositeWheatstoneTerminalSymmetry.vertex oppositeWheatstoneNetwork.source =
      oppositeWheatstoneNetwork.target := by decide

theorem oppositeWheatstone_terminal_symmetry_target :
    oppositeWheatstoneTerminalSymmetry.vertex oppositeWheatstoneNetwork.target =
      oppositeWheatstoneNetwork.source := by decide

end Universality
