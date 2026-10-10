import Universality.Geometry.MetricDirectLimit
import Mathlib.Data.Nat.Basic

namespace Universality.Geometry.IsometricSequence
noncomputable section

variable (Space : ℕ → Type*) [∀ depth, MetricSpace (Space depth)]
variable (next : ∀ depth, Space depth ↪ Space (depth + 1))

def transition (first second : ℕ) (bound : first ≤ second) : Space first ↪ Space second where
  toFun := Nat.leRecOn (C := Space) bound (fun {depth} => next depth)
  inj' := Nat.leRecOn_injective bound (fun {depth} => next depth) (fun depth => (next depth).injective)

instance directedSystem : DirectedSystem Space
    (fun {first second} bound => transition Space next first second bound) where
  map_self := by
    intro index point
    exact Nat.leRecOn_self point
  map_map := by
    intro third second first firstBound secondBound point
    exact (Nat.leRecOn_trans firstBound secondBound point).symm

theorem transition_isometry (hnext : ∀ depth, Isometry (next depth))
    (first second : ℕ) (bound : first ≤ second) :
    Isometry (transition Space next first second bound) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (Nat.leRecOn (C := Space) bound (fun {depth} => next depth) x)
    (Nat.leRecOn (C := Space) bound (fun {depth} => next depth) y) = dist x y
  induction second, bound using Nat.le_induction with
  | base => rw [Nat.leRecOn_self, Nat.leRecOn_self]
  | succ second bound ih =>
    rw [Nat.leRecOn_succ bound, Nat.leRecOn_succ bound, (hnext second).dist_eq, ih]

abbrev limitMetricSpace (hnext : ∀ depth, Isometry (next depth)) :
    MetricSpace (DirectLimit Space (transition Space next)) :=
  MetricDirectLimit.metricSpace Space (transition Space next)
    (transition_isometry Space next hnext)

theorem completion_inclusion_isometry (hnext : ∀ depth, Isometry (next depth))
    (depth : ℕ) :
    letI := limitMetricSpace Space next hnext
    Isometry (fun point : Space depth =>
      ((⟦⟨depth, point⟩⟧ : DirectLimit Space (transition Space next)) :
        UniformSpace.Completion (DirectLimit Space (transition Space next)))) :=
  MetricDirectLimit.completion_inclusion_isometry Space (transition Space next)
    (transition_isometry Space next hnext) depth

end
end Universality.Geometry.IsometricSequence

