import IGSIII34.Spectral.TransitionTrajectoryCompletion20261011

/-! The transition from a retained discrete prefix to any later coordinate
is the original semigroup kernel for the full elapsed time, proved by
composing the actual successive kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNReal

variable {Space : Type*} [MeasurableSpace Space]
  (transition : ℝ≥0 → Kernel Space Space)
  [∀ time, IsMarkovKernel (transition time)]

theorem transitionTrajectory_partial_future_completion20261011
    (zero : transition 0 = Kernel.id)
    (addition : ∀ first second, (transition second) ∘ₖ (transition first) = transition (first+second))
    (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule)
    (first second : ℕ) (below : first ≤ second) :
    (Kernel.partialTraj (X := fun _ => Space)
      (transitionTrajectoryStepCompletion20261011 transition schedule) first second).map
        (fun history => history ⟨second, Finset.mem_Iic.mpr le_rfl⟩) =
      (transition (schedule second - schedule first)).comap
        (fun history : Finset.Iic first → Space => history ⟨first, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  induction second, below using Nat.le_induction with
  | base =>
    rw [Kernel.partialTraj_self, tsub_self, zero, Kernel.id_map, Kernel.id_comap]
  | succ second below inductionHypothesis =>
    rw [Kernel.partialTraj_succ_eq_comp below, Kernel.map_comp,
      Kernel.map_partialTraj_succ_self]
    change (transition (schedule (second+1) - schedule second)).comap
      (fun history : Finset.Iic second → Space => history ⟨second, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _) ∘ₖ
      Kernel.partialTraj (X := fun _ => Space) (transitionTrajectoryStepCompletion20261011 transition schedule) first second = _
    rw [← Kernel.comp_map _ _ (f := fun history : Finset.Iic second → Space => history ⟨second, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop), inductionHypothesis,
      ← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_assoc, addition]
    have elapsed : (schedule second - schedule first) + (schedule (second+1) - schedule second) =
        schedule (second+1) - schedule first := by
      rw [add_comm, tsub_add_tsub_cancel (scheduleMonotone second.le_succ) (scheduleMonotone below)]
    rw [elapsed, Kernel.comp_deterministic_eq_comap]

theorem transitionTrajectory_future_completion20261011
    (zero : transition 0 = Kernel.id)
    (addition : ∀ first second, (transition second) ∘ₖ (transition first) = transition (first+second))
    (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule)
    (first second : ℕ) (below : first ≤ second) :
    (Kernel.traj (X := fun _ => Space)
      (transitionTrajectoryStepCompletion20261011 transition schedule) first).map
        (fun path => path second) =
      (transition (schedule second - schedule first)).comap
        (fun history : Finset.Iic first → Space => history ⟨first, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  have evaluation : (fun path : ℕ → Space => path second) =
      (fun history : Finset.Iic second → Space => history ⟨second, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe second := rfl
  rw [evaluation, Kernel.map_comp_right _ (measurable_frestrictLe second) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe]
  exact transitionTrajectory_partial_future_completion20261011 transition zero addition schedule scheduleMonotone first second below

end
end IGSIII34.Spectral
