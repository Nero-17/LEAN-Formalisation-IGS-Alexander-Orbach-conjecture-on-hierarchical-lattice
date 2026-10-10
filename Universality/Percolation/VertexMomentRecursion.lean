import Universality.Percolation.VertexMassMoments
import Universality.Graph.TerminalSymmetricRule
import Universality.Probability.BranchingMoments

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem TerminalSymmetric.generation {rule : Rule} (h : rule.TerminalSymmetric) (n : ℕ) :
    (rule.generation n).TerminalSymmetric := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.mul h

theorem generation_conditionalVertexMoment (rule : Rule) (hsymmetric : rule.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n r : ℕ) (state : LiveState) :
    (rule.generation (n + 1)).network.conditionalVertexMoment p state r =
      branchingMomentOperator
        (fun state => rule.network.conditionalCellWeight p (state == .connected))
        (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
        rule.network.childState
        (fun state r => (rule.generation n).network.conditionalVertexMoment p state r) r state := by
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric.generation n
  unfold conditionalVertexMoment
  rw [rule.generation_conditionalInternalMoment p hp hp' hfixed n r]
  simp_rw [rule.network.child_conditionalVertexMoment (rule.generation n).network symmetry hs ht p
    (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n])]
  simp only [branchingMomentOperator, assignmentMomentSum, branchingChildMoment, conditionalVertexMoment]
  apply Finset.sum_congr rfl
  intro configuration _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.prod_congr rfl
  intro edge _
  cases rule.network.childState state configuration edge <;> rfl

end
end Universality.Rule
