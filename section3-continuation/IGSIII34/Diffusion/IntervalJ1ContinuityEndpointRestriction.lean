import IGSIII34.Diffusion.IntervalTimeChangeRestriction
import IGSIII34.Diffusion.IntervalFiniteKnotsCompletion20261011
import IGSIII34.Diffusion.SkorokhodContinuousLimitCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def intervalPathRestriction (terminal : SkorokhodIntervalTimeCompletion20261011)
    (path : SkorokhodIntervalPathCompletion20261011 Space) :
    SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => path (intervalScaledTime terminal time)⟩

/-- Restriction in J1 needs continuity only at the new endpoint, not on
the whole path. A small tail correction to the actual time change fixes
the endpoint and leaves the entire earlier part of the path unchanged. -/
theorem intervalPathRestriction_continuousAt_endpoint
    (terminal : SkorokhodIntervalTimeCompletion20261011)
    (terminalPositive : 0 < terminal.val) (terminalInterior : terminal.val < 1)
    (path : SkorokhodIntervalPathCompletion20261011 Space)
    (endpointContinuous : ContinuousAt path.toFun terminal) :
    ContinuousAt (intervalPathRestriction terminal) path := by
  apply Metric.continuousAt_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨duration, durationPositive, endpointClose⟩ :=
    Metric.continuousAt_iff.mp endpointContinuous (tolerance / 8) (by positivity)
  let tailLength := min (duration / 4) (terminal.val / 4)
  have tailPositive : 0 < tailLength := lt_min (by positivity) (by positivity)
  have tailDuration : tailLength ≤ duration / 4 := min_le_left _ _
  have tailTerminal : tailLength ≤ terminal.val / 4 := min_le_right _ _
  let pivot : SkorokhodIntervalTimeCompletion20261011 :=
    ⟨terminal.val - tailLength, ⟨by linarith, by linarith [terminal.property.2]⟩⟩
  let error := min (tailLength / 2) (min (terminal.val * tolerance / 8) (tolerance / 8))
  have errorPositive : 0 < error := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have errorTail : error ≤ tailLength / 2 := min_le_left _ _
  have errorTime : error ≤ terminal.val * tolerance / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have errorSpatial : error ≤ tolerance / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨error, errorPositive, ?_⟩
  intro first near
  have nearEDistance : skorokhodJ1EDistCompletion20261011 first path < ENNReal.ofReal error := edist_lt_ofReal.mpr near
  obtain ⟨change, changeSmall⟩ := iInf_lt_iff.mp nearEDistance
  have timeSmall (time : SkorokhodIntervalTimeCompletion20261011) : dist (change time) time < error := by
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (change next) next) time).trans (le_max_left _ _)).trans_lt changeSmall
  have spatialSmall (time : SkorokhodIntervalTimeCompletion20261011) : dist (first (change time)) (path time) < error := by
    apply edist_lt_ofReal.mp
    exact ((le_iSup (fun next => edist (first (change next)) (path next)) time).trans (le_max_right _ _)).trans_lt changeSmall
  have inverseNear : dist (change.symm terminal) terminal < error := by
    simpa only [change.apply_symm_apply, dist_comm] using timeSmall (change.symm terminal)
  have inverseReal := abs_lt.mp inverseNear
  have pivotBefore : pivot < terminal := by change terminal.val - tailLength < terminal.val; linarith
  have pivotBeforeInverse : pivot < change.symm terminal := by
    change terminal.val - tailLength < (change.symm terminal).val
    change -error < (change.symm terminal).val - terminal.val ∧
      (change.symm terminal).val - terminal.val < error at inverseReal
    linarith
  have inverseInterior : (change.symm terminal).val < 1 := by
    have upper := change.symm.strictMono
      (show terminal < (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion20261011) from terminalInterior)
    rwa [intervalOrderIso_one_fixed_completion20261011] at upper
  obtain ⟨correction, correctionTerminal, correctionFixed, correctionBound⟩ :=
    interval_single_knot_orderIso_completion20261011 pivot terminal (change.symm terminal)
      pivotBefore pivotBeforeInverse terminalInterior inverseInterior
  let corrected := correction.trans change
  have correctedTerminal : corrected terminal = terminal := by
    change change (correction terminal) = terminal
    rw [correctionTerminal, change.apply_symm_apply]
  have correctedNear (time : SkorokhodIntervalTimeCompletion20261011) : dist (corrected time) time < 2 * error := by
    have correctionNear : dist (correction time) time < error :=
      (correctionBound time).trans_lt (by simpa only [dist_comm] using inverseNear)
    have triangle := dist_triangle (change (correction time)) (correction time) time
    change dist (change (correction time)) time < _
    linarith [timeSmall (correction time)]
  have restrictedTime (time : SkorokhodIntervalTimeCompletion20261011) :
      dist (intervalRestrictedOrderIso corrected terminal terminalPositive correctedTerminal time) time ≤ tolerance / 2 := by
    have numerator := (correctedNear (intervalScaledTime terminal time)).le
    change |(corrected (intervalScaledTime terminal time)).val - terminal.val * time.val| ≤ 2 * error at numerator
    change |(corrected (intervalScaledTime terminal time)).val / terminal.val - time.val| ≤ _
    have identity : (corrected (intervalScaledTime terminal time)).val / terminal.val - time.val =
        ((corrected (intervalScaledTime terminal time)).val - terminal.val * time.val) / terminal.val := by
      field_simp [terminalPositive.ne']
    rw [identity, abs_div, abs_of_pos terminalPositive]
    apply (div_le_iff₀ terminalPositive).mpr
    nlinarith
  have restrictedSpatial (time : SkorokhodIntervalTimeCompletion20261011) :
      dist (intervalPathRestriction terminal first
        (intervalRestrictedOrderIso corrected terminal terminalPositive correctedTerminal time))
        (intervalPathRestriction terminal path time) ≤ tolerance / 2 := by
    change dist (first (intervalScaledTime terminal
      (intervalRestrictedOrderIso corrected terminal terminalPositive correctedTerminal time)))
      (path (intervalScaledTime terminal time)) ≤ _
    rw [intervalRestrictedOrderIso_scaled_apply]
    let present := intervalScaledTime terminal time
    change dist (first (change (correction present))) (path present) ≤ _
    by_cases before : present ≤ pivot
    · rw [correctionFixed present before]
      exact (spatialSmall present).le.trans (by linarith)
    · have presentUpper : present ≤ terminal := intervalScaledTime_le_terminal terminal time
      have presentClose : dist present terminal < duration := by
        change |present.val - terminal.val| < duration
        apply abs_lt.mpr
        change ¬ present.val ≤ terminal.val - tailLength at before
        change present.val ≤ terminal.val at presentUpper
        constructor <;> linarith
      have correctedLower : pivot < correction present := by
        have lower := correction.strictMono (lt_of_not_ge before)
        rwa [correctionFixed pivot le_rfl] at lower
      have correctedUpper : correction present ≤ change.symm terminal := by
        have upper := correction.monotone presentUpper
        rwa [correctionTerminal] at upper
      have correctionClose : dist (correction present) terminal < duration := by
        change |(correction present).val - terminal.val| < duration
        apply abs_lt.mpr
        change terminal.val - tailLength < (correction present).val at correctedLower
        change (correction present).val ≤ (change.symm terminal).val at correctedUpper
        constructor <;> linarith
      have firstClose := spatialSmall (correction present)
      have middleClose := endpointClose correctionClose
      have lastClose := endpointClose presentClose
      have triangle := dist_triangle (first (change (correction present))) (path (correction present)) (path present)
      have middleTriangle := dist_triangle (path (correction present)) (path terminal) (path present)
      rw [dist_comm (path terminal) (path present)] at middleTriangle
      linarith
  have edistance : edist (intervalPathRestriction terminal first) (intervalPathRestriction terminal path) ≤
      ENNReal.ofReal (tolerance / 2) := by
    apply iInf_le_of_le (intervalRestrictedOrderIso corrected terminal terminalPositive correctedTerminal)
    apply max_le
    · apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (restrictedTime time)
    · apply iSup_le
      intro time
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (restrictedSpatial time)
  exact ((edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp edistance).trans_lt (by linarith)

end
end IGSIII34.Diffusion
