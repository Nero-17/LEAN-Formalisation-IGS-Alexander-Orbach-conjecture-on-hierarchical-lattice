import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Constructed infinite trajectories of a transition semigroup at an
ordered countable schedule. The path measure is the genuine Ionescu–Tulcea
measure, and its regular conditional law is the supplied transition kernel.
No process-existence assumption is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory NNReal

variable {Space : Type*} [MeasurableSpace Space]
  (transition : ℝ≥0 → Kernel Space Space)
  [∀ time, IsMarkovKernel (transition time)]

def transitionTrajectoryStepCompletion20261011 (schedule : ℕ → ℝ≥0)
    (index : ℕ) : Kernel ((_: Finset.Iic index) → Space) Space :=
  (transition (schedule (index+1) - schedule index)).comap
    (fun history => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance transitionTrajectoryStep_isMarkov_completion20261011
    (schedule : ℕ → ℝ≥0) (index : ℕ) :
    IsMarkovKernel (transitionTrajectoryStepCompletion20261011 transition schedule index) :=
  inferInstanceAs (IsMarkovKernel ((transition (schedule (index+1) - schedule index)).comap
    (fun history : Finset.Iic index → Space => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)))

theorem transitionTrajectoryStep_apply_completion20261011
    (schedule : ℕ → ℝ≥0) (index : ℕ) (history : Finset.Iic index → Space) :
    transitionTrajectoryStepCompletion20261011 transition schedule index history =
      transition (schedule (index+1) - schedule index) (history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) := rfl

def transitionTrajectoryLawCompletion20261011 (initial : Measure Space)
    [IsProbabilityMeasure initial] (schedule : ℕ → ℝ≥0) :
    ProbabilityMeasure (ℕ → Space) :=
  ⟨Kernel.trajMeasure ((transition (schedule 0)) ∘ₘ initial)
    (transitionTrajectoryStepCompletion20261011 transition schedule), inferInstance⟩

theorem transitionTrajectoryLaw_conditional_completion20261011
    [StandardBorelSpace Space] [Nonempty Space]
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (index : ℕ) :
    condDistrib (fun path : ℕ → Space => path (index+1)) (frestrictLe index)
      (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)) =ᵐ[
        (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map (frestrictLe index)]
      transitionTrajectoryStepCompletion20261011 transition schedule index :=
  Kernel.condDistrib_trajMeasure

theorem transitionTrajectoryLaw_successor_joint_completion20261011
    (initial : Measure Space) [IsProbabilityMeasure initial]
    (schedule : ℕ → ℝ≥0) (index : ℕ) :
    ((transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
      (frestrictLe index)) ⊗ₘ transitionTrajectoryStepCompletion20261011 transition schedule index =
    (transitionTrajectoryLawCompletion20261011 transition initial schedule : Measure (ℕ → Space)).map
      (fun path => (frestrictLe index path, path (index+1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end
end IGSIII34.Spectral
