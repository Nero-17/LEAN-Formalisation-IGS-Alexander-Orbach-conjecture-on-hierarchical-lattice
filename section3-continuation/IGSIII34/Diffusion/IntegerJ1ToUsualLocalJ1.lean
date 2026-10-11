import IGSIII34.Diffusion.IntervalJ1ContinuityEndpointRestriction
import IGSIII34.Diffusion.UsualLocalJ1SequenceTopology

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

theorem intervalPath_zero_evaluation_lipschitz :
    LipschitzWith 1 (fun path : SkorokhodIntervalPathCompletion20261011 Space =>
      path (⟨0, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011)) := by
  apply LipschitzWith.of_edist_le
  intro first last
  change edist (first _) (last _) ≤ skorokhodJ1EDistCompletion20261011 first last
  apply le_iInf
  intro change
  have bound := le_iSup (fun time => edist (first (change time)) (last time))
    (⟨0, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011)
  rw [intervalOrderIso_zero_fixed_completion20261011] at bound
  exact bound.trans (le_max_right _ _)

theorem intervalConstantPath_lipschitz :
    LipschitzWith 1 (fun point : Space =>
      (⟨fun _ => point⟩ : SkorokhodIntervalPathCompletion20261011 Space)) := by
  apply LipschitzWith.of_edist_le
  intro first last
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  exact le_rfl

/-- Integer-horizon J1 convergence implies the standard local-J1 window
criterion at every cadlag limiting path. Only continuity at the selected
endpoint is used; all other jumps of the limiting path are permitted. -/
theorem integerJ1_tendsto_usualLocalJ1_sequence
    (paths : ℕ → SkorokhodCadlagPathCompletion20261011 Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space)
    (convergence : Tendsto paths atTop (𝓝 path)) :
    usualLocalJ1SequenceConvergence paths path := by
  intro horizon endpointContinuous
  have globalConvergence := continuous_subtype_val.tendsto path |>.comp convergence
  by_cases zero : horizon = 0
  · subst horizon
    have profileConvergence := (skorokhodGlobal_tendsto_iff_completion20261011.mp globalConvergence) 0
    have initialConvergence := intervalPath_zero_evaluation_lipschitz.continuous.tendsto
      (skorokhodIntegerProfileCompletion20261011 path.val 0) |>.comp profileConvergence
    have zeroProfile (candidate : SkorokhodGlobalPathCompletion20261011 Space) :
        (skorokhodIntegerProfileCompletion20261011 candidate 0)
          (⟨0, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011) = candidate 0 := by
      unfold skorokhodIntegerProfileCompletion20261011
      apply congrArg candidate.toFun
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_zero,
        NNReal.coe_mk, Nat.cast_zero, zero_add, one_mul]
      rfl
    have initialActual : Tendsto (fun index => (paths index).val 0) atTop (𝓝 (path.val 0)) := by
      simpa only [Function.comp_def, zeroProfile] using initialConvergence
    have constantConvergence := intervalConstantPath_lipschitz.continuous.tendsto
      (path.val 0) |>.comp initialActual
    simpa only [Function.comp_def, skorokhodHorizonRestrictionCompletion20261011,
      zero_mul, mul_zero] using constantConvergence
  · have horizonPositive : 0 < (horizon : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr zero)
    let count : ℕ := ⌊(horizon : ℝ)⌋₊
    have integerPositive : 0 < (count + 1 : ℝ) := by positivity
    have horizonBefore : (horizon : ℝ) < (count + 1 : ℝ) := Nat.lt_floor_add_one _
    let terminal : SkorokhodIntervalTimeCompletion20261011 :=
      ⟨(horizon : ℝ) / (count + 1 : ℝ),
        ⟨div_nonneg horizon.property integerPositive.le, (div_le_one integerPositive).mpr horizonBefore.le⟩⟩
    have terminalPositive : 0 < terminal.val := div_pos horizonPositive integerPositive
    have terminalInterior : terminal.val < 1 := (div_lt_one integerPositive).mpr horizonBefore
    have physicalTerminal : (count + 1 : ℝ≥0) * ⟨terminal.val, terminal.property.1⟩ = horizon := by
      apply NNReal.eq
      exact mul_div_cancel₀ _ integerPositive.ne'
    have profileContinuous : ContinuousAt
        (skorokhodIntegerProfileCompletion20261011 path.val count).toFun terminal := by
      have continuousAtPhysical : ContinuousAt path.val.toFun
          ((count + 1 : ℝ≥0) * ⟨terminal.val, terminal.property.1⟩) := by
        rwa [physicalTerminal]
      have scaledContinuous : ContinuousAt
          (fun time : SkorokhodIntervalTimeCompletion20261011 =>
            (count + 1 : ℝ≥0) * ⟨time.val, time.property.1⟩) terminal := by fun_prop
      exact ContinuousAt.comp (f := fun time : SkorokhodIntervalTimeCompletion20261011 =>
        (count + 1 : ℝ≥0) * ⟨time.val, time.property.1⟩) continuousAtPhysical scaledContinuous
    have identity (candidate : SkorokhodGlobalPathCompletion20261011 Space) :
        intervalPathRestriction terminal (skorokhodIntegerProfileCompletion20261011 candidate count) =
          skorokhodHorizonRestrictionCompletion20261011 horizon candidate := by
      apply congrArg SkorokhodIntervalPathCompletion20261011.mk
      funext time
      apply congrArg candidate.toFun
      apply NNReal.eq
      change (count + 1 : ℝ) * (((horizon : ℝ) / (count + 1 : ℝ)) * time.val) = (horizon : ℝ) * time.val
      rw [← mul_assoc, mul_div_cancel₀ _ integerPositive.ne']
    have restricted := Filter.Tendsto.comp
      (intervalPathRestriction_continuousAt_endpoint terminal terminalPositive terminalInterior
        (skorokhodIntegerProfileCompletion20261011 path.val count) profileContinuous)
      ((skorokhodGlobal_tendsto_iff_completion20261011.mp globalConvergence) count)
    simpa only [Function.comp_def, identity] using restricted

/-- The identity from the integer-horizon carrier to the local-J1
sequential topology is continuous at all cadlag paths, including paths
jumping at integer endpoints. -/
theorem integerJ1_to_usualLocalJ1_identity_continuous :
    Continuous[inferInstance, usualLocalJ1SequenceTopology (Space := Space)]
      (id : SkorokhodCadlagPathCompletion20261011 Space → SkorokhodCadlagPathCompletion20261011 Space) := by
  apply continuous_def.mpr
  intro set openSet
  change IsOpen set
  have complementClosed : IsSeqClosed setᶜ := by
    intro paths path outside convergence membership
    obtain ⟨index, inside⟩ :=
      (openSet paths path (integerJ1_tendsto_usualLocalJ1_sequence paths path convergence) membership).exists
    exact outside index inside
  simpa only [compl_compl] using complementClosed.isClosed.isOpen_compl

/-- The local-J1 Borel sigma algebra is contained in the original
integer-horizon Borel sigma algebra. Hence local continuous tests are
measurable for every original walk path law without an extra assumption. -/
theorem usualLocalJ1_borel_le_integerJ1_borel :
    @borel (SkorokhodCadlagPathCompletion20261011 Space) usualLocalJ1SequenceTopology ≤
      borel (SkorokhodCadlagPathCompletion20261011 Space) := by
  have topologicalLE : (inferInstance : TopologicalSpace (SkorokhodCadlagPathCompletion20261011 Space)) ≤
      usualLocalJ1SequenceTopology := by
    exact @continuous_id_iff_le (SkorokhodCadlagPathCompletion20261011 Space)
      inferInstance usualLocalJ1SequenceTopology |>.mp integerJ1_to_usualLocalJ1_identity_continuous
  exact @borel_anti (SkorokhodCadlagPathCompletion20261011 Space)
    inferInstance usualLocalJ1SequenceTopology topologicalLE

theorem usualLocalJ1Test_integer_continuous
    (test : SkorokhodCadlagPathCompletion20261011 Space → ℝ)
    (continuity : usualLocalJ1SequentiallyContinuousTest test) : Continuous test := by
  apply continuous_iff_seqContinuous.mpr
  intro paths path convergence
  exact continuity path paths (integerJ1_tendsto_usualLocalJ1_sequence paths path convergence)

theorem usualLocalJ1Test_integer_measurable
    (test : SkorokhodCadlagPathCompletion20261011 Space → ℝ)
    (continuity : usualLocalJ1SequentiallyContinuousTest test) : Measurable test :=
  (usualLocalJ1Test_integer_continuous test continuity).measurable

end
end IGSIII34.Diffusion
