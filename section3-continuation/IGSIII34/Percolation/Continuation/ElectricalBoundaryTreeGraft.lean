import IGSIII34.Percolation.Continuation.ElectricalBoundaryPrefixMean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

def electricalBoundaryTreeGraft (rule : Rule) (depth : ℕ)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 :=
  fun coordinate => ((sample coordinate).1,
    electricalBoundaryTreeIteration rule depth (electricalBoundaryTreeShift rule coordinate.1 sample))

theorem electricalBoundaryTreeGraft_measurable (rule : Rule) (depth : ℕ) :
    Measurable (electricalBoundaryTreeGraft rule depth) :=
  measurable_pi_lambda _ (fun coordinate =>
    (measurable_fst.comp (measurable_pi_apply coordinate)).prodMk
      ((electricalBoundaryTreeIteration_measurable rule depth).comp
        (electricalBoundaryTreeShift_measurable rule coordinate.1)))

theorem electricalBoundaryTreeShift_graft (rule : Rule) (depth : ℕ)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0)
    (address : List (Fin rule.edges)) :
    electricalBoundaryTreeShift rule address (electricalBoundaryTreeGraft rule depth sample) =
      electricalBoundaryTreeGraft rule depth (electricalBoundaryTreeShift rule address sample) := by
  funext coordinate
  apply Prod.ext
  · rfl
  · change electricalBoundaryTreeIteration rule depth
      (electricalBoundaryTreeShift rule (address++coordinate.1) sample) =
        electricalBoundaryTreeIteration rule depth
          (electricalBoundaryTreeShift rule coordinate.1 (electricalBoundaryTreeShift rule address sample))
    rw [electricalBoundaryTreeShift_append]

theorem electricalBoundaryTreeIteration_add (rule : Rule) (first second : ℕ)
    (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) :
    electricalBoundaryTreeIteration rule (first+second) sample =
      electricalBoundaryTreeIteration rule first (electricalBoundaryTreeGraft rule second sample) := by
  induction first generalizing sample with
  | zero =>
      have shiftIdentity : electricalBoundaryTreeShift rule [] sample = sample := by
        funext coordinate
        rfl
      simpa only [Nat.zero_add, electricalBoundaryTreeIteration, electricalBoundaryTreeGraft, shiftIdentity]
  | succ first previous =>
      rw [Nat.succ_add]
      change electricalCellNNReal rule.network (sample ([], true)).1
        (fun edge => electricalBoundaryTreeIteration rule (first+second)
          (electricalBoundaryTreeShift rule [edge] sample)) =
        electricalCellNNReal rule.network (sample ([], true)).1
          (fun edge => electricalBoundaryTreeIteration rule first
            (electricalBoundaryTreeShift rule [edge] (electricalBoundaryTreeGraft rule second sample)))
      congr 1
      funext edge
      rw [electricalBoundaryTreeShift_graft, previous]

end
end IGSIII34.Percolation
