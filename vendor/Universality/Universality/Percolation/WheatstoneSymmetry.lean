import Universality.Percolation.TerminalSymmetry
import Universality.Percolation.Wheatstone

namespace Universality
open FiniteNetwork

def wheatstoneTerminalSymmetry : wheatstoneNetwork.NetworkSymmetry where
  vertex := Equiv.swap 0 1
  edge := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
  endpoint := by decide

theorem wheatstone_terminal_symmetry_source :
    wheatstoneTerminalSymmetry.vertex wheatstoneNetwork.source = wheatstoneNetwork.target := by
  decide

theorem wheatstone_terminal_symmetry_target :
    wheatstoneTerminalSymmetry.vertex wheatstoneNetwork.target = wheatstoneNetwork.source := by
  decide

theorem wheatstone_massMatrix_reverse (p : ℝ) :
    wheatstoneNetwork.reverse.massMatrix p = wheatstoneNetwork.massMatrix p :=
  wheatstoneTerminalSymmetry.massMatrix_reverse wheatstone_terminal_symmetry_source
    wheatstone_terminal_symmetry_target p

end Universality
