import Universality.Geometry.IsometricSequence

/-!
A compatible family of similarities from each level of an isometric sequence
to the next level induces a similarity of the metric direct limit and extends
to its completion. Both the exact distance factor and the values on original
vertices are proved; no ambient chart is assumed.
-/
namespace Universality.Geometry.IsometricSequence
noncomputable section
open UniformSpace
open scoped NNReal

variable (Space : ℕ → Type*)
variable (next : ∀ depth, Space depth ↪ Space (depth + 1))
variable (cell : ∀ depth, Space depth → Space (depth + 1))
variable (hnatural : ∀ depth point,
  next (depth + 1) (cell depth point) = cell (depth + 1) (next depth point))

include hnatural in
theorem cell_transition (first second : ℕ) (bound : first ≤ second) (point : Space first) :
    transition Space next (first + 1) (second + 1) (Nat.succ_le_succ bound) (cell first point) =
      cell second (transition Space next first second bound point) := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [transition, Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound ih =>
    change Nat.leRecOn (C := Space) (Nat.succ_le_succ (Nat.le_succ_of_le bound))
      (fun {depth} => next depth) (cell first point) =
      cell (second + 1) (Nat.leRecOn (C := Space) (Nat.le_succ_of_le bound)
        (fun {depth} => next depth) point)
    rw [Nat.leRecOn_succ (Nat.succ_le_succ bound), Nat.leRecOn_succ bound]
    change next (second + 1)
      (transition Space next (first + 1) (second + 1) _ (cell first point)) =
      cell (second + 1) (next second (transition Space next first second bound point))
    rw [ih, hnatural]

def limitCell : DirectLimit Space (transition Space next) → DirectLimit Space (transition Space next) :=
  DirectLimit.lift (transition Space next)
    (fun depth point => ⟦⟨depth + 1, cell depth point⟩⟧)
    (fun first second bound point => by
      calc
        _ = ⟦⟨second + 1, transition Space next (first + 1) (second + 1)
          (Nat.succ_le_succ bound) (cell first point)⟩⟧ :=
            DirectLimit.eq_of_le ⟨first + 1, cell first point⟩ (second + 1) (Nat.succ_le_succ bound)
        _ = _ := congrArg (fun value : Space (second + 1) =>
          (⟦⟨second + 1, value⟩⟧ : DirectLimit Space (transition Space next)))
          (cell_transition Space next cell hnatural first second bound point))

@[simp] theorem limitCell_mk (depth : ℕ) (point : Space depth) :
    limitCell Space next cell hnatural ⟦⟨depth, point⟩⟧ = ⟦⟨depth + 1, cell depth point⟩⟧ := rfl

variable [∀ depth, MetricSpace (Space depth)]
variable (hnext : ∀ depth, Isometry (next depth))


theorem limitCell_dist (contraction : ℝ)
    (hdist : ∀ depth first second, dist (cell depth first) (cell depth second) =
      contraction * dist first second)
    (first second : DirectLimit Space (transition Space next)) :
    letI := limitMetricSpace Space next hnext
    dist (limitCell Space next cell hnatural first) (limitCell Space next cell hnatural second) =
      contraction * dist first second := by
  letI := limitMetricSpace Space next hnext
  refine DirectLimit.induction₂ (transition Space next) (fun depth first second => ?_) first second
  rw [limitCell_mk, limitCell_mk]
  change MetricDirectLimit.compatibleDistance _ _ _ _ _ =
    contraction * MetricDirectLimit.compatibleDistance _ _ _ _ _
  rw [MetricDirectLimit.compatibleDistance_mk, MetricDirectLimit.compatibleDistance_mk]
  exact hdist depth first second

theorem limitCell_lipschitz (contraction : ℝ≥0)
    (hdist : ∀ depth first second, dist (cell depth first) (cell depth second) =
      contraction * dist first second) :
    letI := limitMetricSpace Space next hnext
    LipschitzWith contraction (limitCell Space next cell hnatural) := by
  letI := limitMetricSpace Space next hnext
  exact LipschitzWith.of_dist_le_mul (fun first second =>
    le_of_eq (limitCell_dist Space next cell hnatural hnext contraction hdist first second))

def completionCell : letI := limitMetricSpace Space next hnext
    Completion (DirectLimit Space (transition Space next)) →
      Completion (DirectLimit Space (transition Space next)) := by
  letI := limitMetricSpace Space next hnext
  exact Completion.map (limitCell Space next cell hnatural)

@[simp] theorem completionCell_mk (contraction : ℝ≥0)
    (hdist : ∀ depth first second, dist (cell depth first) (cell depth second) =
      contraction * dist first second) (depth : ℕ) (point : Space depth) :
    letI := limitMetricSpace Space next hnext
    completionCell Space next cell hnatural hnext
      ((⟦⟨depth, point⟩⟧ : DirectLimit Space (transition Space next)) : Completion _) =
      ((⟦⟨depth + 1, cell depth point⟩⟧ : DirectLimit Space (transition Space next)) : Completion _) := by
  letI := limitMetricSpace Space next hnext
  exact Completion.map_coe
    (limitCell_lipschitz Space next cell hnatural hnext contraction hdist).uniformContinuous _

theorem completionCell_dist (contraction : ℝ≥0)
    (hdist : ∀ depth first second, dist (cell depth first) (cell depth second) =
      contraction * dist first second) :
    letI := limitMetricSpace Space next hnext
    ∀ first second : Completion (DirectLimit Space (transition Space next)),
    dist (completionCell Space next cell hnatural hnext first)
      (completionCell Space next cell hnatural hnext second) = contraction * dist first second := by
  letI := limitMetricSpace Space next hnext
  intro first second
  have huniform := (limitCell_lipschitz Space next cell hnatural hnext contraction hdist).uniformContinuous
  refine Completion.induction_on₂ first second
    (isClosed_eq (by simp only [completionCell]; fun_prop) (by fun_prop)) ?_
  intro first second
  simp only [completionCell, Completion.map_coe huniform, Completion.dist_eq]
  exact limitCell_dist Space next cell hnatural hnext contraction hdist first second
end
end Universality.Geometry.IsometricSequence