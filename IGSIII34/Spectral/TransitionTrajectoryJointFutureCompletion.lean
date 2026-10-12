import IGSIII34.Spectral.TransitionTrajectoryFutureCompletion
import IGSIII34.Spectral.TransitionTrajectoryMarginalsCompletion
import IGSIII34.Spectral.KernelDeterministicMarginalCompletion

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNReal

variable {Space : Type*} [MeasurableSpace Space]
  (transition : ℝ≥0 → Kernel Space Space)
  [∀ time, IsMarkovKernel (transition time)]

theorem transitionTrajectoryLaw_disintegration_completion
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (index : ℕ) :
    (Kernel.traj (X := fun _ => Space)
      (transitionTrajectoryStepCompletion transition schedule) index) ∘ₘ
      ((transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)).map
        (frestrictLe index)) =
    (transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)) := by
  change (Kernel.traj (X := fun _ => Space) (transitionTrajectoryStepCompletion transition schedule) index) ∘ₘ
    ((Kernel.trajMeasure (X := fun _ => Space) ((transition (schedule 0)) ∘ₘ initial)
      (transitionTrajectoryStepCompletion transition schedule)).map (frestrictLe index)) =
      Kernel.trajMeasure (X := fun _ => Space) ((transition (schedule 0)) ∘ₘ initial)
        (transitionTrajectoryStepCompletion transition schedule)
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe index), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Kernel.traj_comp_partialTraj (Nat.zero_le index)]

theorem transitionTrajectoryLaw_future_joint_completion
    [MeasurableSingletonClass Space]
    (zero : transition 0 = Kernel.id)
    (addition : ∀ first second, (transition second) ∘ₖ (transition first) = transition (first+second))
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule)
    (first second : ℕ) (below : first ≤ second) :
    (transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)).map
      (fun path => (frestrictLe first path, path second)) =
    ((transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)).map
      (frestrictLe first)) ⊗ₘ
      (transition (schedule second - schedule first)).comap
        (fun history : Finset.Iic first → Space => history ⟨first, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  have fixedPrefix : (Kernel.traj (X := fun _ => Space)
      (transitionTrajectoryStepCompletion transition schedule) first).map (frestrictLe first) = Kernel.id := by
    rw [Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  have paired := kernel_pair_eq_of_identity_marginal_completion
    (Kernel.traj (X := fun _ => Space) (transitionTrajectoryStepCompletion transition schedule) first)
    (frestrictLe first) (measurable_frestrictLe first) (fun path => path second) (measurable_pi_apply second) fixedPrefix
  rw [transitionTrajectory_future_completion transition zero addition schedule scheduleMonotone first second below] at paired
  have disintegration := transitionTrajectoryLaw_disintegration_completion transition initial schedule first
  calc
    _ = ((Kernel.traj (X := fun _ => Space)
      (transitionTrajectoryStepCompletion transition schedule) first) ∘ₘ
      ((transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)).map
        (frestrictLe first))).map (fun path => (frestrictLe first path, path second)) := by rw [disintegration]
    _ = _ := by
      rw [Measure.map_comp _ _ ((measurable_frestrictLe first).prodMk (measurable_pi_apply second)), paired,
        ← Measure.compProd_eq_comp_prod]

theorem transitionTrajectoryLaw_future_conditional_completion
    [MeasurableSingletonClass Space] [StandardBorelSpace Space] [Nonempty Space]
    (zero : transition 0 = Kernel.id)
    (addition : ∀ first second, (transition second) ∘ₖ (transition first) = transition (first+second))
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule)
    (first second : ℕ) (below : first ≤ second) :
    condDistrib (fun path : ℕ → Space => path second) (frestrictLe first)
      (transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)) =ᵐ[
        (transitionTrajectoryLawCompletion transition initial schedule : Measure (ℕ → Space)).map (frestrictLe first)]
      (transition (schedule second - schedule first)).comap
        (fun history : Finset.Iic first → Space => history ⟨first, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_frestrictLe first) (measurable_pi_apply second)
  exact transitionTrajectoryLaw_future_joint_completion transition zero addition initial schedule scheduleMonotone first second below

end
end IGSIII34.Spectral
