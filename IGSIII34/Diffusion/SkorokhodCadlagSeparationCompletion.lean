import IGSIII34.Diffusion.SkorokhodCadlagSampleCompletion
import IGSIII34.Diffusion.IntervalFiniteKnotsCompletion
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

theorem skorokhodInterval_rightContinuous_separates_completion
    (first second : SkorokhodIntervalPathCompletion Space)
    (firstRight : ∀ time, ContinuousWithinAt first (Ici time) time)
    (secondRight : ∀ time, ContinuousWithinAt second (Ici time) time)
    (zero : edist first second = 0) : first = second := by
  apply congrArg SkorokhodIntervalPathCompletion.mk
  funext time
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro tolerance positive
  have changeExists (error : ℝ) (errorPositive : 0 < error) :
      ∃ change : SkorokhodIntervalTimeCompletion ≃o SkorokhodIntervalTimeCompletion,
        skorokhodTimeChangeErrorCompletion first second change < ENNReal.ofReal error := by
    have small : skorokhodJ1EDistCompletion first second < ENNReal.ofReal error := by
      change edist first second < _
      rw [zero]
      exact ENNReal.ofReal_pos.mpr errorPositive
    exact iInf_lt_iff.mp small
  by_cases terminal : time.val = 1
  · obtain ⟨change, changeSmall⟩ := changeExists tolerance positive
    have same : change time = time := by
      have identity : time = (⟨1, by norm_num⟩ : SkorokhodIntervalTimeCompletion) := Subtype.ext terminal
      rw [identity, intervalOrderIso_one_fixed_completion]
    have spatial : edist (first (change time)) (second time) < ENNReal.ofReal tolerance :=
      ((le_iSup (fun next => edist (first (change next)) (second next)) time).trans (le_max_right _ _)).trans_lt changeSmall
    rw [same] at spatial
    simpa only [zero_add] using (edist_lt_ofReal.mp spatial).le
  · have before : time.val < 1 := lt_of_le_of_ne time.property.2 terminal
    obtain ⟨firstDuration, firstPositive, firstClose⟩ :=
      Metric.continuousWithinAt_iff.mp (firstRight time) (tolerance/3) (by positivity)
    obtain ⟨secondDuration, secondPositive, secondClose⟩ :=
      Metric.continuousWithinAt_iff.mp (secondRight time) (tolerance/3) (by positivity)
    let duration : ℝ := min firstDuration (min secondDuration (1-time.val))
    have durationPositive : 0 < duration := lt_min firstPositive (lt_min secondPositive (by linarith))
    have durationFirst : duration ≤ firstDuration := min_le_left _ _
    have durationSecond : duration ≤ secondDuration := (min_le_right _ _).trans (min_le_left _ _)
    have durationEnd : duration ≤ 1-time.val := (min_le_right _ _).trans (min_le_right _ _)
    let next : SkorokhodIntervalTimeCompletion :=
      ⟨time.val+duration/2, ⟨by linarith [time.property.1], by linarith⟩⟩
    have nextAfter : time ≤ next := by change time.val ≤ time.val+duration/2; linarith
    have nextDistance : dist next time = duration/2 := by
      change |(time.val+duration/2)-time.val| = duration/2
      rw [add_sub_cancel_left, abs_of_pos (by positivity)]
    let error : ℝ := min (duration/4) (tolerance/3)
    have errorPositive : 0 < error := lt_min (by positivity) (by positivity)
    obtain ⟨change, changeSmall⟩ := changeExists error errorPositive
    have timeSmall : dist (change next) next < duration/4 := by
      have bound : edist (change next) next < ENNReal.ofReal error :=
        ((le_iSup (fun point => edist (change point) point) next).trans (le_max_left _ _)).trans_lt changeSmall
      exact (edist_lt_ofReal.mp bound).trans_le (min_le_left _ _)
    have changedAfter : time ≤ change next := by
      change time.val ≤ (change next).val
      change |(change next).val - (time.val+duration/2)| < duration/4 at timeSmall
      have lower := (abs_lt.mp timeSmall).1
      linarith
    have firstNear := firstClose changedAfter (show dist (change next) time < firstDuration from
      (dist_triangle _ _ _).trans_lt (by rw [nextDistance]; linarith))
    have secondNear := secondClose nextAfter (show dist next time < secondDuration from by rw [nextDistance]; linarith)
    have spatial : dist (first (change next)) (second next) < tolerance/3 := by
      have bound : edist (first (change next)) (second next) < ENNReal.ofReal error :=
        ((le_iSup (fun point => edist (first (change point)) (second point)) next).trans (le_max_right _ _)).trans_lt changeSmall
      exact (edist_lt_ofReal.mp bound).trans_le (min_le_right _ _)
    have triangle := (dist_triangle (first time) (first (change next)) (second time)).trans
      (add_le_add le_rfl (dist_triangle (first (change next)) (second next) (second time)))
    rw [dist_comm (first (change next)) (first time)] at firstNear
    simpa only [zero_add] using (show dist (first time) (second time) ≤ tolerance by linarith)

theorem skorokhodIntegerProfile_rightContinuous_completion
    (path : SkorokhodCadlagPathCompletion Space) (horizon : ℕ)
    (time : SkorokhodIntervalTimeCompletion) :
    ContinuousWithinAt (skorokhodIntegerProfileCompletion path.val horizon) (Ici time) time := by
  let scaleTime : SkorokhodIntervalTimeCompletion → ℝ≥0 := fun point =>
    (horizon+1 : ℝ≥0) * ⟨point.val, point.property.1⟩
  have continuous : Continuous scaleTime := by fun_prop
  have maps : MapsTo scaleTime (Ici time) (Ici (scaleTime time)) := by
    intro point after
    change (horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩ ≤ (horizon+1 : ℝ≥0) * ⟨point.val, point.property.1⟩
    exact mul_le_mul_of_nonneg_left after (by positivity)
  exact (path.property.1 (scaleTime time)).comp continuous.continuousWithinAt maps

theorem skorokhodCadlag_dist_separates_completion
    (first second : SkorokhodCadlagPathCompletion Space) (zero : dist first second = 0) : first = second := by
  have globalZero : dist first.val second.val = 0 := zero
  have indistinguishable := Metric.inseparable_iff.mpr globalZero
  have profiles (horizon : ℕ) : skorokhodIntegerProfileCompletion first.val horizon =
      skorokhodIntegerProfileCompletion second.val horizon := by
    have continuous : Continuous (fun path : SkorokhodGlobalPathCompletion Space =>
        skorokhodIntegerProfileCompletion path horizon) :=
      (continuous_apply horizon).comp skorokhodIntegerProfile_inducing_completion.continuous
    have profileZero := (indistinguishable.map continuous).edist_eq_zero
    exact skorokhodInterval_rightContinuous_separates_completion _ _
      (skorokhodIntegerProfile_rightContinuous_completion first horizon)
      (skorokhodIntegerProfile_rightContinuous_completion second horizon) profileZero
  apply Subtype.ext
  apply congrArg SkorokhodGlobalPathCompletion.mk
  funext time
  let horizon : ℕ := ⌊(time : ℝ)⌋₊
  have positive : 0 < (horizon+1 : ℝ) := by positivity
  let unitTime : SkorokhodIntervalTimeCompletion :=
    ⟨(time : ℝ)/(horizon+1 : ℝ), ⟨by positivity, (div_le_one positive).mpr (Nat.lt_floor_add_one _).le⟩⟩
  have identity : (horizon+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩ = time := by
    apply NNReal.eq
    change (horizon+1 : ℝ) * ((time : ℝ)/(horizon+1 : ℝ)) = time
    exact mul_div_cancel₀ _ positive.ne'
  have point := congrArg (fun path : SkorokhodIntervalPathCompletion Space => path unitTime) (profiles horizon)
  change first.val ((horizon+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩) =
    second.val ((horizon+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩) at point
  rwa [identity] at point

@[reducible] def skorokhodCadlagMetricCompletion : MetricSpace (SkorokhodCadlagPathCompletion Space) :=
  {toPseudoMetricSpace := inferInstance,
    eq_of_dist_eq_zero := fun zero => skorokhodCadlag_dist_separates_completion _ _ zero}

end
end IGSIII34.Diffusion
