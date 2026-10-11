import Mathlib.Order.DirectedInverseSystem
import Mathlib.Topology.MetricSpace.Completion

/-!
A metric and its complete isometric realisation are constructed for a directed
system of metric spaces with isometric transition maps. No ambient realisation
or dimension conclusion is assumed. This construction applies to the actual
rescaled generation metrics.
-/

namespace Universality.Geometry.MetricDirectLimit
noncomputable section

variable {Index : Type*} [Preorder Index] [IsDirectedOrder Index]
variable (Space : Index → Type*) [∀ index, MetricSpace (Space index)]
variable (transition : ∀ first second : Index, first ≤ second → Space first ↪ Space second)
variable [DirectedSystem Space (fun {first second} bound => transition first second bound)]
variable (hisometry : ∀ first second bound, Isometry (transition first second bound))

def compatibleDistance : DirectLimit Space transition → DirectLimit Space transition → ℝ :=
  DirectLimit.lift₂ transition transition (fun _ => dist)
    (fun first second bound x y => (hisometry first second bound).dist_eq x y |>.symm)

theorem compatibleDistance_mk (index : Index) (x y : Space index) :
    compatibleDistance Space transition hisometry ⟦⟨index, x⟩⟧ ⟦⟨index, y⟩⟧ = dist x y :=
  DirectLimit.lift₂_def ..

abbrev metricSpace : MetricSpace (DirectLimit Space transition) where
  dist := compatibleDistance Space transition hisometry
  dist_self x := DirectLimit.induction transition
    (fun index point => by rw [compatibleDistance_mk]; exact dist_self point) x
  dist_comm x y := DirectLimit.induction₂ transition
    (fun index first second => by rw [compatibleDistance_mk, compatibleDistance_mk]; exact dist_comm first second) x y
  dist_triangle x y z := DirectLimit.induction₃ transition
    (fun index first second third => by
      rw [compatibleDistance_mk, compatibleDistance_mk, compatibleDistance_mk]
      exact dist_triangle first second third) x y z
  eq_of_dist_eq_zero := by
    intro x y
    refine DirectLimit.induction₂ transition (fun index first second => ?_) x y
    intro hequal
    rw [compatibleDistance_mk] at hequal
    exact congrArg (fun point : Space index => (⟦⟨index, point⟩⟧ : DirectLimit Space transition))
      (dist_eq_zero.mp hequal)

theorem inclusion_isometry (index : Index) :
    letI := metricSpace Space transition hisometry
    Isometry (fun point : Space index => (⟦⟨index, point⟩⟧ : DirectLimit Space transition)) := by
  letI := metricSpace Space transition hisometry
  apply Isometry.of_dist_eq
  intro x y
  exact compatibleDistance_mk Space transition hisometry index x y

theorem completion_inclusion_isometry (index : Index) :
    letI := metricSpace Space transition hisometry
    Isometry (fun point : Space index =>
      ((⟦⟨index, point⟩⟧ : DirectLimit Space transition) :
        UniformSpace.Completion (DirectLimit Space transition))) := by
  letI := metricSpace Space transition hisometry
  exact UniformSpace.Completion.coe_isometry.comp
    (inclusion_isometry Space transition hisometry index)

end
end Universality.Geometry.MetricDirectLimit

