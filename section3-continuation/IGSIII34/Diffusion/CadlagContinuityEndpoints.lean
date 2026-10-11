import IGSIII34.Diffusion.UsualLocalJ1PathLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set MeasureTheory
open scoped Topology NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def cadlagLeftJumpBox
    (path : SkorokhodCadlagPathCompletion20261011 Space) (level : ℕ) (lower : ℚ) : Set ℝ≥0 :=
  {time | 0 ≤ (lower : ℝ) ∧ (lower : ℝ) < time ∧ ∃ leftValue : Space,
    4 * (1 / (level + 1 : ℝ)) ≤ dist leftValue (path.val time) ∧
    ∀ previous : ℝ≥0, (lower : ℝ) < previous → previous < time →
      dist (path.val previous) leftValue < 1 / (level + 1 : ℝ)}

theorem cadlagLeftJumpBox_subsingleton
    (path : SkorokhodCadlagPathCompletion20261011 Space) (level : ℕ) (lower : ℚ) :
    (cadlagLeftJumpBox path level lower).Subsingleton := by
  have tolerancePositive : 0 < 1 / (level + 1 : ℝ) := by positivity
  have cannotIncrease (first second : ℝ≥0)
      (firstMember : first ∈ cadlagLeftJumpBox path level lower)
      (secondMember : second ∈ cadlagLeftJumpBox path level lower) : ¬ first < second := by
    intro increasing
    obtain ⟨lowerNonnegative, lowerFirst, firstLeft, firstJump, firstNear⟩ := firstMember
    obtain ⟨_, lowerSecond, secondLeft, secondJump, secondNear⟩ := secondMember
    let previous : ℝ≥0 := ⟨((lower : ℝ) + (first : ℝ)) / 2,
      div_nonneg (add_nonneg lowerNonnegative first.property) (by norm_num)⟩
    have previousAfter : (lower : ℝ) < previous := by change _ < ((lower : ℝ) + (first : ℝ)) / 2; linarith
    have previousBefore : previous < first := by
      apply NNReal.coe_lt_coe.mp
      change ((lower : ℝ) + (first : ℝ)) / 2 < (first : ℝ)
      linarith
    have firstClose := firstNear previous previousAfter previousBefore
    have secondClose := secondNear previous previousAfter (previousBefore.trans increasing)
    have valueClose := secondNear first lowerFirst increasing
    have triangle := (dist_triangle firstLeft (path.val previous) (path.val first)).trans
      (add_le_add le_rfl (dist_triangle (path.val previous) secondLeft (path.val first)))
    rw [dist_comm firstLeft (path.val previous), dist_comm secondLeft (path.val first)] at triangle
    linarith
  intro first firstMember second secondMember
  exact le_antisymm (not_lt.mp (cannotIncrease second first secondMember firstMember))
    (not_lt.mp (cannotIncrease first second firstMember secondMember))

theorem cadlag_positive_discontinuities_countable
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    {time : ℝ≥0 | 0 < time ∧ ¬ ContinuousAt path.val.toFun time}.Countable := by
  apply (countable_iUnion (fun level => countable_iUnion (fun lower =>
    (cadlagLeftJumpBox_subsingleton path level lower).countable))).mono
  intro time membership
  obtain ⟨positive, discontinuous⟩ := membership
  obtain ⟨leftValue, leftConvergence⟩ := path.property.2 time positive
  have leftDifferent : leftValue ≠ path.val time := by
    intro equality
    apply discontinuous
    have leftContinuous : ContinuousWithinAt path.val.toFun (Iio time) time := by
      change Tendsto path.val.toFun (𝓝[Iio time] time) (𝓝 (path.val time))
      simpa only [equality] using leftConvergence
    have unionContinuous := leftContinuous.union (path.property.1 time)
    simpa only [Iio_union_Ici, continuousWithinAt_univ] using unionContinuous
  have jumpPositive : 0 < dist leftValue (path.val time) := dist_pos.mpr leftDifferent
  obtain ⟨level, levelSmall⟩ := exists_nat_one_div_lt (show 0 < dist leftValue (path.val time) / 4 by positivity)
  have tolerancePositive : 0 < 1 / (level + 1 : ℝ) := by positivity
  have close : {previous : ℝ≥0 | dist (path.val previous) leftValue < 1 / (level + 1 : ℝ)} ∈
      𝓝[Iio time] time := leftConvergence.eventually (Metric.ball_mem_nhds leftValue tolerancePositive)
  obtain ⟨neighbourhood, neighbourhoodMem, neighbourhoodSubset⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp close
  obtain ⟨duration, durationPositive, ballSubset⟩ := Metric.mem_nhds_iff.mp neighbourhoodMem
  have lowerBefore : max 0 ((time : ℝ) - duration / 2) < (time : ℝ) :=
    max_lt_iff.mpr ⟨NNReal.coe_pos.mpr positive, by linarith⟩
  obtain ⟨lower, lowerAfter, lowerTime⟩ := exists_rat_btwn lowerBefore
  have lowerNonnegative : 0 ≤ (lower : ℝ) := (le_max_left _ _).trans lowerAfter.le
  apply mem_iUnion.mpr
  refine ⟨level, mem_iUnion.mpr ⟨lower, lowerNonnegative, lowerTime, leftValue, ?_, ?_⟩⟩
  · linarith
  · intro previous previousAfter previousBefore
    apply neighbourhoodSubset
    constructor
    · apply ballSubset
      change dist previous time < duration
      rw [NNReal.dist_eq, abs_of_neg (sub_neg.mpr (NNReal.coe_lt_coe.mpr previousBefore))]
      have lowerDuration := (le_max_right _ _).trans_lt lowerAfter
      linarith
    · exact previousBefore

/-- Every positive open physical-time interval contains a continuity
endpoint of the cadlag path. -/
theorem cadlag_exists_continuity_endpoint
    (path : SkorokhodCadlagPathCompletion20261011 Space)
    (lower upper : ℝ≥0) (ordered : lower < upper) :
    ∃ time : ℝ≥0, lower < time ∧ time < upper ∧ ContinuousAt path.val.toFun time := by
  have countable := (cadlag_positive_discontinuities_countable path).image
    (fun time : ℝ≥0 => (time : ℝ))
  by_contra failure
  push_neg at failure
  have inclusion : Ioo (lower : ℝ) upper ⊆
      (fun time : ℝ≥0 => (time : ℝ)) '' {time : ℝ≥0 | 0 < time ∧ ¬ ContinuousAt path.val.toFun time} := by
    intro time between
    have positive : 0 < time := lt_of_le_of_lt lower.property between.1
    let endpoint : ℝ≥0 := ⟨time, positive.le⟩
    exact ⟨endpoint, ⟨NNReal.coe_pos.mp positive,
      failure endpoint (NNReal.coe_lt_coe.mp between.1) (NNReal.coe_lt_coe.mp between.2)⟩, rfl⟩
  have measureLE := measure_mono (μ := (volume : Measure ℝ)) inclusion
  rw [countable.measure_zero volume, Real.volume_Ioo] at measureLE
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr
    (sub_pos.mpr (NNReal.coe_lt_coe.mpr ordered)))) measureLE

end
end IGSIII34.Diffusion
