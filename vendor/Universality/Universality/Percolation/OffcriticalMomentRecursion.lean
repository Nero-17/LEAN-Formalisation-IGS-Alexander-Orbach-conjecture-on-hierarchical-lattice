import Universality.Percolation.UniqueFixedPoint
import Universality.Percolation.VertexMomentRecursion
import Universality.Graph.ClassicalSubstitution

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem Classical.generation_conditionalVertexMoment_offcritical {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (n order : ℕ) (state : LiveState) :
    (rule.generation (n + 1)).network.conditionalVertexMoment p state order =
      branchingMomentOperator
        (fun state => rule.network.conditionalCellWeight ((rule.generation n).network.reliability p) (state == .connected))
        (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
        rule.network.childState
        (fun state order => (rule.generation n).network.conditionalVertexMoment p state order) order state := by
  have hpositive := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr
    ((h.generation n).connected _)
  have hless := (rule.generation n).network.reliability_lt_one hp hp'
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  unfold conditionalVertexMoment
  rw [← (rule.generationTopDecomposition n).conditionalInternalMoment]
  rw [rule.network.conditionalInternalMoment_substitute (rule.generation n).network p hpositive hless]
  simp_rw [rule.network.child_conditionalVertexMoment (rule.generation n).network symmetry hs ht p hpositive hless]
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

