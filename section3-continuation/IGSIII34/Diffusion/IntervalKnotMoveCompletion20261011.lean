import IGSIII34.Diffusion.SkorokhodJ1TopologyCompletion20261011
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open Set
open scoped Topology

/-- An elementary increasing piecewise affine map. It fixes the interval
below the preceding knot, moves one interior knot, and fixes the endpoint. -/
def intervalKnotMoveRealCompletion20261011 (previous source target time : ℝ) : ℝ :=
  if time ≤ previous then time
  else if time ≤ source then
    previous + (time - previous) * ((target - previous) / (source - previous))
  else target + (time - source) * ((1 - target) / (1 - source))

theorem intervalKnotMoveReal_strictMono_completion20261011
    (previous source target : ℝ) (sourceAbove : previous < source)
    (targetAbove : previous < target) (sourceBelow : source < 1)
    (targetBelow : target < 1) :
    StrictMono (intervalKnotMoveRealCompletion20261011 previous source target) := by
  have leftPositive : 0 < (target - previous) / (source - previous) :=
    div_pos (sub_pos.mpr targetAbove) (sub_pos.mpr sourceAbove)
  have rightPositive : 0 < (1 - target) / (1 - source) :=
    div_pos (sub_pos.mpr targetBelow) (sub_pos.mpr sourceBelow)
  have leftIdentity : (source - previous) * ((target - previous) / (source - previous)) = target - previous := by
    field_simp
  intro first last increasing
  by_cases firstLower : first ≤ previous
  · by_cases lastLower : last ≤ previous
    · simpa [intervalKnotMoveRealCompletion20261011, firstLower, lastLower] using increasing
    · by_cases lastMiddle : last ≤ source
      · have productPositive := mul_pos (sub_pos.mpr (lt_of_not_ge lastLower)) leftPositive
        simp only [intervalKnotMoveRealCompletion20261011, if_pos firstLower, if_neg lastLower, if_pos lastMiddle]
        linarith
      · have productPositive := mul_pos (sub_pos.mpr (lt_of_not_ge lastMiddle)) rightPositive
        simp only [intervalKnotMoveRealCompletion20261011, if_pos firstLower, if_neg lastLower, if_neg lastMiddle]
        linarith
  · have lastLower : ¬ last ≤ previous := by linarith
    by_cases firstMiddle : first ≤ source
    · by_cases lastMiddle : last ≤ source
      · have productPositive := mul_pos (sub_pos.mpr increasing) leftPositive
        simp only [intervalKnotMoveRealCompletion20261011, if_neg firstLower, if_neg lastLower,
          if_pos firstMiddle, if_pos lastMiddle]
        nlinarith
      · have firstBound := mul_le_mul_of_nonneg_right (show first - previous ≤ source - previous by linarith) leftPositive.le
        have lastProduct := mul_pos (sub_pos.mpr (lt_of_not_ge lastMiddle)) rightPositive
        simp only [intervalKnotMoveRealCompletion20261011, if_neg firstLower, if_neg lastLower,
          if_pos firstMiddle, if_neg lastMiddle]
        linarith
    · have lastMiddle : ¬ last ≤ source := by linarith
      have productPositive := mul_pos (sub_pos.mpr increasing) rightPositive
      simp only [intervalKnotMoveRealCompletion20261011, if_neg firstLower, if_neg lastLower,
        if_neg firstMiddle, if_neg lastMiddle]
      nlinarith

theorem intervalKnotMoveReal_continuous_completion20261011
    (previous source target : ℝ) (sourceAbove : previous < source)
    (sourceBelow : source < 1) :
    Continuous (intervalKnotMoveRealCompletion20261011 previous source target) := by
  have sourceNonzero : source - previous ≠ 0 := ne_of_gt (sub_pos.mpr sourceAbove)
  have endNonzero : 1 - source ≠ 0 := ne_of_gt (sub_pos.mpr sourceBelow)
  have middleContinuous : Continuous (fun time : ℝ =>
      if time ≤ source then previous + (time - previous) * ((target - previous) / (source - previous))
      else target + (time - source) * ((1 - target) / (1 - source))) := by
    apply Continuous.if
    · intro time boundary
      have equal : time = source := by simpa only [Set.setOf_le, frontier_Iic, mem_singleton_iff] using boundary
      subst time
      field_simp
      <;> ring
    · fun_prop
    · fun_prop
  unfold intervalKnotMoveRealCompletion20261011
  apply Continuous.if
  · intro time boundary
    have equal : time = previous := by simpa only [Set.setOf_le, frontier_Iic, mem_singleton_iff] using boundary
    subst time
    simp [sourceAbove.le]
  · exact continuous_id
  · exact middleContinuous

theorem intervalKnotMoveReal_zero_completion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous) :
    intervalKnotMoveRealCompletion20261011 previous source target 0 = 0 := by
  simp [intervalKnotMoveRealCompletion20261011, previousNonnegative]

theorem intervalKnotMoveReal_one_completion20261011
    (previous source target : ℝ) (sourceAbove : previous < source)
    (sourceBelow : source < 1) :
    intervalKnotMoveRealCompletion20261011 previous source target 1 = 1 := by
  have previousBelow : ¬ 1 ≤ previous := by linarith
  have sourceNotAbove : ¬ 1 ≤ source := not_le.mpr sourceBelow
  have denominator : 1 - source ≠ 0 := ne_of_gt (sub_pos.mpr sourceBelow)
  simp only [intervalKnotMoveRealCompletion20261011, if_neg previousBelow, if_neg sourceNotAbove]
  field_simp
  <;> ring

def intervalKnotMoveCompletion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous)
    (sourceAbove : previous < source) (targetAbove : previous < target)
    (sourceBelow : source < 1) (targetBelow : target < 1) :
    SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011 := by
  let function : SkorokhodIntervalTimeCompletion20261011 → SkorokhodIntervalTimeCompletion20261011 :=
    fun time => ⟨intervalKnotMoveRealCompletion20261011 previous source target time,
      by
        have monotone := (intervalKnotMoveReal_strictMono_completion20261011 previous source target sourceAbove targetAbove sourceBelow targetBelow).monotone
        constructor
        · simpa [intervalKnotMoveReal_zero_completion20261011 previous source target previousNonnegative] using monotone time.property.1
        · simpa [intervalKnotMoveReal_one_completion20261011 previous source target sourceAbove sourceBelow] using monotone time.property.2⟩
  have increasing : StrictMono function := by
    intro first last inequality
    exact intervalKnotMoveReal_strictMono_completion20261011 previous source target sourceAbove targetAbove sourceBelow targetBelow inequality
  have onto : Function.Surjective function := by
    intro time
    have intermediate := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      (intervalKnotMoveReal_continuous_completion20261011 previous source target sourceAbove sourceBelow).continuousOn
    have inImage : (time : ℝ) ∈ (intervalKnotMoveRealCompletion20261011 previous source target) '' Icc 0 1 := by
      apply intermediate
      simpa [intervalKnotMoveReal_zero_completion20261011 previous source target previousNonnegative,
        intervalKnotMoveReal_one_completion20261011 previous source target sourceAbove sourceBelow] using time.property
    obtain ⟨original, inside, equal⟩ := inImage
    exact ⟨⟨original, inside⟩, Subtype.ext equal⟩
  exact (Equiv.ofBijective function ⟨increasing.injective, onto⟩).toOrderIso
    increasing.monotone (by
      intro first last inequality
      apply increasing.le_iff_le.mp
      simpa only [Equiv.apply_symm_apply] using inequality)

theorem intervalKnotMove_apply_completion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous)
    (sourceAbove : previous < source) (targetAbove : previous < target)
    (sourceBelow : source < 1) (targetBelow : target < 1)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    ((intervalKnotMoveCompletion20261011 previous source target previousNonnegative sourceAbove targetAbove sourceBelow targetBelow time) : ℝ) =
      intervalKnotMoveRealCompletion20261011 previous source target time := rfl

theorem intervalKnotMove_fixed_lower_completion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous)
    (sourceAbove : previous < source) (targetAbove : previous < target)
    (sourceBelow : source < 1) (targetBelow : target < 1)
    (time : SkorokhodIntervalTimeCompletion20261011) (lower : (time : ℝ) ≤ previous) :
    intervalKnotMoveCompletion20261011 previous source target previousNonnegative sourceAbove targetAbove sourceBelow targetBelow time = time := by
  apply Subtype.ext
  simp [intervalKnotMove_apply_completion20261011, intervalKnotMoveRealCompletion20261011, lower]

theorem intervalKnotMove_source_completion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous)
    (sourceAbove : previous < source) (targetAbove : previous < target)
    (sourceBelow : source < 1) (targetBelow : target < 1)
    (sourceTime targetTime : SkorokhodIntervalTimeCompletion20261011)
    (sourceEqual : (sourceTime : ℝ) = source) (targetEqual : (targetTime : ℝ) = target) :
    intervalKnotMoveCompletion20261011 previous source target previousNonnegative sourceAbove targetAbove sourceBelow targetBelow sourceTime = targetTime := by
  apply Subtype.ext
  rw [intervalKnotMove_apply_completion20261011, sourceEqual, targetEqual]
  have denominator : source - previous ≠ 0 := ne_of_gt (sub_pos.mpr sourceAbove)
  simp only [intervalKnotMoveRealCompletion20261011, if_neg (not_le.mpr sourceAbove), if_pos le_rfl]
  field_simp
  <;> ring

theorem intervalKnotMove_distance_completion20261011
    (previous source target : ℝ) (previousNonnegative : 0 ≤ previous)
    (sourceAbove : previous < source) (targetAbove : previous < target)
    (sourceBelow : source < 1) (targetBelow : target < 1)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    dist (intervalKnotMoveCompletion20261011 previous source target previousNonnegative sourceAbove targetAbove sourceBelow targetBelow time) time ≤ |source - target| := by
  rw [Subtype.dist_eq, Real.dist_eq, intervalKnotMove_apply_completion20261011]
  by_cases lower : (time : ℝ) ≤ previous
  · simp [intervalKnotMoveRealCompletion20261011, lower]
  · by_cases middle : (time : ℝ) ≤ source
    · have denominator : source - previous ≠ 0 := ne_of_gt (sub_pos.mpr sourceAbove)
      have ratioNonnegative : 0 ≤ ((time : ℝ) - previous) / (source - previous) :=
        div_nonneg (by linarith) (sub_pos.mpr sourceAbove).le
      have ratioAtMostOne : ((time : ℝ) - previous) / (source - previous) ≤ 1 :=
        (div_le_one (sub_pos.mpr sourceAbove)).mpr (by linarith)
      have difference : intervalKnotMoveRealCompletion20261011 previous source target time - time =
          (target - source) * (((time : ℝ) - previous) / (source - previous)) := by
        simp only [intervalKnotMoveRealCompletion20261011, if_neg lower, if_pos middle]
        field_simp
        <;> ring
      rw [difference, abs_mul, abs_of_nonneg ratioNonnegative, abs_sub_comm]
      exact mul_le_of_le_one_right (abs_nonneg _) ratioAtMostOne
    · have denominator : 1 - source ≠ 0 := ne_of_gt (sub_pos.mpr sourceBelow)
      have ratioNonnegative : 0 ≤ (1 - (time : ℝ)) / (1 - source) :=
        div_nonneg (sub_nonneg.mpr time.property.2) (sub_pos.mpr sourceBelow).le
      have ratioAtMostOne : (1 - (time : ℝ)) / (1 - source) ≤ 1 :=
        (div_le_one (sub_pos.mpr sourceBelow)).mpr (by linarith)
      have difference : intervalKnotMoveRealCompletion20261011 previous source target time - time =
          (target - source) * ((1 - (time : ℝ)) / (1 - source)) := by
        simp only [intervalKnotMoveRealCompletion20261011, if_neg lower, if_neg middle]
        field_simp
        <;> ring
      rw [difference, abs_mul, abs_of_nonneg ratioNonnegative, abs_sub_comm]
      exact mul_le_of_le_one_right (abs_nonneg _) ratioAtMostOne

end
end IGSIII34.Diffusion
