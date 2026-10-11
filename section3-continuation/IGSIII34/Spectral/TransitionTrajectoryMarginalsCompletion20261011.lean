import IGSIII34.Spectral.TransitionTrajectoryCompletion20261011

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

theorem transitionTrajectoryLaw_initial_marginal_completion20261011
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) :
    (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
      (fun path => path 0) = (transition (schedule 0)) ∘ₘ initial := by
  unfold transitionTrajectoryLawCompletion20261011 Kernel.trajMeasure
  change ((Kernel.traj (X := fun _ => Space) (transitionTrajectoryStepCompletion20261011 transition schedule) 0) ∘ₘ
    (((transition (schedule 0)) ∘ₘ initial).map (MeasurableEquiv.piUnique _).symm)).map
      (fun path => path 0) = _
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have evalZero : (fun path : ℕ → Space => path 0) =
      (fun history : Finset.Iic 0 → Space => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := rfl
  rw [evalZero, Kernel.map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map,
    Measure.deterministic_comp_eq_map, Measure.map_map]
  · have same : (fun history : Finset.Iic 0 → Space => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Space)).symm = id := by
      funext point
      rfl
    rw [same, Measure.map_id]
  · exact measurable_pi_apply _
  · exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Space)).symm.measurable
  · exact measurable_pi_apply _

theorem transitionTrajectoryLaw_successor_marginal_completion20261011
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (index : ℕ) :
    (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
      (fun path => path (index+1)) =
    (transition (schedule (index+1) - schedule index)) ∘ₘ
      ((transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
        (fun path => path index)) := by
  have joint := congrArg Measure.snd
    (transitionTrajectoryLaw_successor_joint_completion20261011 transition initial schedule index)
  rw [Measure.snd_compProd] at joint
  change _ = ((transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
    (fun path => (frestrictLe index path, path (index+1)))).map Prod.snd at joint
  rw [Measure.map_map measurable_snd (by fun_prop)] at joint
  change _ = (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map (fun path => path (index+1)) at joint
  rw [← joint]
  have currentMap : ((transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map (fun path => path index)) =
      (((transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
        (frestrictLe index)).map (fun history : Finset.Iic index → Space => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩)) := by
    exact (Measure.map_map
      (μ := (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)))
      (g := fun history : Finset.Iic index → Space => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩)
      (f := frestrictLe index) (by fun_prop) (measurable_frestrictLe index)).symm
  rw [currentMap, ← Measure.deterministic_comp_eq_map (measurable_pi_apply _),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
  rfl

theorem transitionTrajectoryLaw_marginal_completion20261011
    (zero : transition 0 = Kernel.id)
    (addition : ∀ first second, (transition second) ∘ₖ (transition first) = transition (first+second))
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule) (index : ℕ) :
    (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
      (fun path => path index) = transition (schedule index) ∘ₘ initial := by
  induction index with
  | zero => exact transitionTrajectoryLaw_initial_marginal_completion20261011 transition initial schedule
  | succ index inductionHypothesis =>
    rw [transitionTrajectoryLaw_successor_marginal_completion20261011 transition initial schedule index,
      inductionHypothesis, Measure.comp_assoc, addition,
      add_tsub_cancel_of_le (scheduleMonotone index.le_succ)]

end
end IGSIII34.Spectral
