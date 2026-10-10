import Universality.Probability.InitialMomentComparison
import Universality.Percolation.OffcriticalMomentRecursion
import Universality.Percolation.RenormalisationLimits

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem Classical.postexit_moment_initial_comparison {rule : Rule} (h : rule.Classical)
    (p exitParameter : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hexit : 0 < exitParameter) (hexit' : exitParameter < 1)
    (offset : ℕ) (hparameter : rule.network.reliability^[offset] p = exitParameter)
    (scale : ℝ) (hscale : 1 ≤ scale) (order : ℕ)
    (hbase : ∀ state k, k ≤ order →
      (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) :
    ∀ n state k, k ≤ order →
      (rule.generation (offset + n)).network.conditionalVertexMoment p state k ≤
        scale ^ k * (rule.generation n).network.conditionalVertexMoment exitParameter state k := by
  have hcrossing (n : ℕ) : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  apply branching_moment_initial_comparison
    (fun n state => rule.network.conditionalCellWeight ((rule.generation n).network.reliability exitParameter) (state == .connected))
    (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
    rule.network.childState
    (fun n state k => (rule.generation (offset + n)).network.conditionalVertexMoment p state k)
    (fun n state k => (rule.generation n).network.conditionalVertexMoment exitParameter state k)
  · intro n state configuration
    exact rule.network.conditionalCellWeight_nonneg
      ((rule.generation n).network.reliability_nonneg hexit.le hexit'.le)
      ((rule.generation n).network.reliability_le_one hexit.le hexit'.le) _ _
  · intro state configuration
    exact Nat.cast_nonneg _
  · intro n state k
    exact (rule.generation (offset + n)).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ _
  · intro n state k
    exact (rule.generation n).network.conditionalInternalMoment_nonneg exitParameter hexit.le hexit'.le _ _ _ _
  · intro n state
    exact (rule.generation (offset + n)).network.conditionalInternalMoment_zero p
      (((rule.generation (offset + n)).network.reliability_pos_iff_connected hp hp').mpr ((h.generation (offset + n)).connected _))
      ((rule.generation (offset + n)).network.reliability_lt_one hp hp') _ _ _
  · intro n state
    exact (rule.generation n).network.conditionalInternalMoment_zero exitParameter
      (((rule.generation n).network.reliability_pos_iff_connected hexit hexit').mpr ((h.generation n).connected _))
      ((rule.generation n).network.reliability_lt_one hexit hexit') _ _ _
  · exact hscale
  · exact hbase
  · intro n state k
    rw [← Nat.add_assoc, h.generation_conditionalVertexMoment_offcritical p hp hp', hcrossing]
  · intro n state k
    exact h.generation_conditionalVertexMoment_offcritical exitParameter hexit hexit' n k state

end
end Universality.Rule
