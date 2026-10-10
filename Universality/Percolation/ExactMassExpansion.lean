import Universality.Percolation.FiniteMassDimension
import Universality.Matrix.TwoByTwoExpansion

namespace Universality
noncomputable section
open Matrix FiniteNetwork

theorem massPlane_power_connected_entry (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (n : ℕ) :
    (M ^ n) .connected .connected = (massPlaneBlock M ^ n) 0 0 := by
  rw [← massPlaneBlock_pow M hplane n]
  rfl

theorem massMatrix_power_connected_expansion (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (hblock : ∀ i j, 0 < massPlaneBlock M i j) (n : ℕ) :
    (M ^ n) .connected .connected =
      ((M .connected .connected - secondaryRoot (massPlaneBlock M)) /
        (positiveRoot (massPlaneBlock M) - secondaryRoot (massPlaneBlock M))) *
          positiveRoot (massPlaneBlock M) ^ n +
      ((positiveRoot (massPlaneBlock M) - M .connected .connected) /
        (positiveRoot (massPlaneBlock M) - secondaryRoot (massPlaneBlock M))) *
          secondaryRoot (massPlaneBlock M) ^ n := by
  rw [massPlane_power_connected_entry M hplane n, twoByTwo_mass_entry_expansion _ hblock n]
  rfl

namespace Rule

theorem exact_conditional_cluster_mass (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (hsymmetric : rule.TerminalSymmetric)
    (hconnected : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (hcut : ∀ edge, rule.network.crosses (onlyClosed edge) = true) (n : ℕ) :
    (rule.generation n).network.conditionalClusterMass p .connected =
      ((rule.network.massMatrix p .connected .connected -
          secondaryRoot (massPlaneBlock (rule.network.massMatrix p))) /
        (positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          secondaryRoot (massPlaneBlock (rule.network.massMatrix p)))) *
            positiveRoot (massPlaneBlock (rule.network.massMatrix p)) ^ (n + 1) +
      ((positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          rule.network.massMatrix p .connected .connected) /
        (positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          secondaryRoot (massPlaneBlock (rule.network.massMatrix p)))) *
            secondaryRoot (massPlaneBlock (rule.network.massMatrix p)) ^ (n + 1) := by
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric
  rw [generation_conditionalClusterMass rule p hfixed hp hp' symmetry hs ht n .connected]
  apply massMatrix_power_connected_expansion
  · exact rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  · exact (rule.network.massPlaneBlock_pos_of_geometry hp hp' hconnected hscale hcut).1

end Rule
end
end Universality
